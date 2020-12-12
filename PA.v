Require Import MetaCoq.Checker.Checker.
From MetaCoq.Template Require Import utils All Pretty.
Require Import List String.
Import MonadNotation.
Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import VectorTech.
Require Import Lia.

(*Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import VectorTech.
Require Import List.
Require Import Lia.*)
Require Import GeneralReflection.
(* I follow the treatment of Peter Smith in "Introduction to Gödel's Theorems"
 (page 37) *)


(* Define the non-logical symbols used in the language of PA *)

Inductive PA_funcs : Type :=
  Zero : PA_funcs
| Succ : PA_funcs
| Plus : PA_funcs
| Mult : PA_funcs.

Definition PA_funcs_ar (f : PA_funcs ) :=
match f with
 | Zero => 0
 | Succ => 1
 | Plus => 2
 | Mult => 2
 end.

Inductive PA_preds : Type :=
  Eq : PA_preds.

Definition PA_preds_ar (P : PA_preds) :=
match P with
 | Eq => 2
end.


Instance PA_funcs_signature : funcs_signature :=
{| syms := PA_funcs ; ar_syms := PA_funcs_ar |}.

Instance PA_preds_signature : preds_signature :=
{| preds := PA_preds ; ar_preds := PA_preds_ar |}.

 
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Notation zero := (func Zero (Vector.nil term)).
Notation "'σ' x" := (func Succ (Vector.cons x (Vector.nil term))) (at level 37).
Notation "x '⊕' y" := (func Plus (Vector.cons x (Vector.cons y (Vector.nil term))) ) (at level 39).
Notation "x '⊗' y" := (func Mult (Vector.cons x (Vector.cons y (Vector.nil term))) ) (at level 38).
Notation "x '==' y" := (atom Eq (Vector.cons term x 1 (Vector.cons term y 0 (Vector.nil term))) ) (at level 40).


Fixpoint num n :=
  match n with
    O => zero
  | S x => σ (num x)
  end.

                      


(* formulate axioms of PA (see page 92) *)

Definition ax_zero_succ := ∀    zero == σ var 0 --> fal.
Definition ax_succ_inj :=  ∀ ∀  σ $1 == σ $0 --> $1 == $0.
Definition ax_add_zero :=  ∀    zero ⊕ $0 == $0.
Definition ax_add_rec :=   ∀ ∀  (σ $0) ⊕ $1 == σ ($0 ⊕ $1).
Definition ax_mult_zero := ∀    zero ⊗ $0 == zero.
Definition ax_mult_rec :=  ∀ ∀  σ $1 ⊗ $0 == $0 ⊕ $1 ⊗ $0.


Definition PA_induction (phi : form) :=
  phi[zero..] --> (∀ phi --> phi[σ $0 .: S >> var]) --> ∀ phi.
Definition phi := $0 == $1.
Compute (phi[zero..]).
Compute (phi[zero .: S >> var]).

(* substitutes t for the variable $0 and leaves all other variables unchanged *)
Definition var0_subst (t : term) : nat -> term :=
  fun n => match n with 0 => t | S n => var (S n) end.


(* var0_subst can be expressed with scons and funcomp *)
Lemma var0_subst_spec t n :
  var0_subst t n = (t .: S >> var) n.
Proof.
  now destruct n as [].
Qed.




                                              

(*** Working in models of PA ***)
                                              
Section Models.                                              
  

  Variable D' : Type.
  Context {I : interp D'}.
  (* Careful: Define this with implicit arguments being maximally evaluated. So use D' and 2, not D or (ar_syms Eq) *)
  Definition Equality := forall v, @i_P _ _ D' I Eq v <-> Vector.hd v = Vector.hd (Vector.tl v). 
  Hypothesis equality : forall v:Vector.t D' 2, @i_P _ _ D' I Eq v <-> Vector.hd v = Vector.hd (Vector.tl v).

  Instance PA_reflector : tarski_reflector := buildDefaultTarski (i_f (f:=Zero) (Vector.nil D')) (fun k => match k with (tVar "D'") => true | _ => false end).
  (* The following predicate expresses that a model satisfies the minimal axioms of PA i.e. all axioms except S x <> 0 *)
  Definition sat_PA_minimal_axioms :=
    forall rho,
      rho ⊨ ax_succ_inj
      /\ rho ⊨ ax_add_zero
      /\ rho ⊨ ax_add_rec
      /\ rho ⊨ ax_mult_zero
      /\ rho ⊨ ax_mult_rec
      /\ (forall phi, rho ⊨ (PA_induction phi) ).      


  Definition sat_PA_axioms :=
    sat_PA_minimal_axioms /\ forall rho, rho ⊨ ax_zero_succ.


  
  Lemma PAeq_sym : forall rho a b, rho ⊨ (a == b) -> rho ⊨ (b == a).
  Proof.
    intros rho a b H. apply equality. cbn. apply equality in H. cbn in H. auto.
  Qed.

  
  Lemma PAeq_trans : forall rho a b c, rho ⊨ (a == b) /\ rho ⊨ (b == c) -> rho ⊨ (a == c).
  Proof.
    intros rho a b c. cbn. rewrite !equality. cbn. intros [C B]. now rewrite C, B.
  Qed.
  Check @i_f.
  Notation iO := (@i_f PA_funcs_signature PA_preds_signature D' I Zero (Vector.nil D')).
  Notation "'iσ' d" := (@i_f _ _ D' I Succ (Vector.cons d (Vector.nil D'))) (at level 37).
  Notation "x 'i⊕' y" := (@i_f _ _ D' I Plus (Vector.cons x (Vector.cons y (Vector.nil D')))) (at level 39).
  Notation "x 'i⊗' y" := (@i_f _ _ D' I Mult (Vector.cons x (Vector.cons y (Vector.nil D')))) (at level 38).
  Notation "x 'i=' y" := (@i_P _ _ _ _ Eq (Vector.cons x (Vector.cons y (Vector.nil D')))) (at level 40).
  Definition iμ k := iter (fun x => iσ x) k iO.
Definition k := (iO i= iO).
Print k.
  Section ReflectionExtension.
    Definition mergeMu (rho:nat -> D) (n:nat) : representsF (iμ n) (num n) rho.
    Proof. unfold representsF. induction n.
    * easy.
    * cbn. do 2 f_equal. cbn in IHn. now rewrite IHn.
    Defined.
    MetaCoq Quote Definition qMu := iμ.
    MetaCoq Quote Definition qMergeMu := mergeMu.
    MetaCoq Quote Definition qMergeTermMu := @num.

    Definition mergeEqProp (rho:nat -> D) (d1 d2 : D) (t1 t2 : term) : representsF d1 t1 rho -> representsF d2 t2 rho -> @representsP _ 0 (t1==t2) rho (d1 = d2).
    Proof. intros pt1 pt2. cbn. unfold representsF in pt1, pt2. cbn in pt1, pt2. rewrite pt1, pt2. now rewrite equality.
    Defined.
    Definition mEq := (constructForm Eq).
    MetaCoq Quote Definition qMergeFormEq := @mEq.
    MetaCoq Quote Definition qMergeEqProp := mergeEqProp.
    Definition reifyCoqEq : baseConnectiveReifier := fun proof tct l fuel envTerm env fPR fTR => match l with [tv; x; y] => if maybeD tct tv then
                                               xr <- fTR proof tct x envTerm env ;;
                                               yr<-  fTR proof tct y envTerm env ;; 
                                               ret (mergeTwoE proof envTerm qMergeFormEq qMergeEqProp x y xr yr)
                                           else fail "Eq applied to wrong type" | _ => fail "Eq constructor applied to != 2 terms" end.
    Definition varsCoqEq : baseConnectiveVars := fun lst fuel tct _ fUVT => match lst with [tv; x; y] => if maybeD tct tv then
                                               xr <- fUVT x;;
                                               yr <- fUVT y;;
                                               ret (xr++yr) else fail "Eq applied to wrong type" | _ => fail "Eq constructor applied to != 2 terms" end.
    Definition reifyBLC (s:string) : baseConnectiveReifier := match s with "eq" => reifyCoqEq | _ => fun _ _ _ _ _ _ _ _ => fail ("Unknown connective " ++ s) end.
    Definition varsBLC (s:string) : baseConnectiveVars := match s with "eq" => varsCoqEq | _ => fun _ _ _ _ _ => fail ("Unknown connective " ++ s) end.
    Definition findVarsTerm : termFinderVars := fun fuel t fUVT => match t with (tApp qMu ([k])) => ret nil | _ => fail "Fail" end.
    Definition reifyTerm : termFinderReifier := fun proof tct fuel t envTerm env fTR => match t with tApp qMu ([k]) => match proof return proofRT proof with true => ret (tApp qMergeTermMu ([k]),(tApp qMergeMu ([envTerm;k]))) | false => ret (tApp qMergeTermMu ([k])) end | _ => fail "Fail" end.
  End ReflectionExtension.
  Instance PA_reflector_ext : tarski_reflector_extensions PA_reflector := {| (*Cannot define instance in section because they are dropped afterwards *)
    baseLogicConnHelper := Some (reifyBLC);
    baseLogicVarHelper := Some (varsBLC);
    termReifierVarHelper := Some (findVarsTerm);
    termReifierReifyHelper := Some (reifyTerm);
    formReifierVarHelper := None;
    formReifierReifyHelper := None
  |}.
 
  (* Test cases *)
  Goal (representableP 0 (iO i= iO)).
  Time represent.
  Qed.
  Goal (representableP 0 (forall d:D', d i= iO)).
  Time represent.
  Qed.
  Goal (representableP 2 (fun a b => a i= b)).
  Time represent. 
  Qed.
  Goal (representableP 2 (fun (d e :D) => forall g, exists j, g i= d i⊕ j /\ False -> False \/ (e i⊗ iO i= iσ j /\ False))).
  Time representNPFast.
  Qed.
  Goal (representableP 0 (forall a b, a i= b)).
  Time represent. 
  Time Qed.
  Goal (representableP 0 (forall a b c, a i= b i⊕ c)).
  Time represent.
  Time Qed.
  Goal (representableP 0 (forall a b c d ,a i= b i⊕ c i⊕ d)).
  Time represent. 
  Time Qed.
  Goal (representableP 0 (forall a b c d e , a i= b i⊕ c i⊕ d i⊕ e)).
  Time represent. 
  Time Qed.
  Goal (representableP 0 (forall a b c d e f , a i= b i⊕ c i⊕ d i⊕ e i⊕ f)).
  Time represent. 
  Time Qed.
  Goal (representableP 0 (forall a b c d e f g , a i= b i⊕ c i⊕ d i⊕ e i⊕ f i⊕ g)).
  Time represent.
  Time Qed.
  Goal (representableP 2 (fun a b=> a i= b)).
  Time represent. 
  Time Qed.
  Goal (representableP 3 (fun a b c=> a i= b i⊕ c)).
  Time represent.
  Time Qed.
  Goal (representableP 4 (fun a b c d =>a i= b i⊕ c i⊕ d)).
  Time represent. 
  Time Qed.
  Goal (representableP 5 (fun a b c d e => a i= b i⊕ c i⊕ d i⊕ e)).
  Time represent. 
  Time Qed.
  Goal (representableP 6 (fun a b c d e f => a i= b i⊕ c i⊕ d i⊕ e i⊕ f)).
  Time represent. 
  Time Qed.
  Goal (representableP 7 (fun a b c d e f g => a i= b i⊕ c i⊕ d i⊕ e i⊕ f i⊕ g)).
  Time represent.
  Time Qed.

  (* Test cases NP*)
  Goal (representableP 0 (iO i= iO)).
  Time representNP.
  Time Qed.
  Goal (representableP 0 (forall d, d i= iO)).
  Time representNP.
  Time Qed.
  Goal (representableP 2 (fun a b => a i= b)).
  Time representNP. 
  Time Qed.
  Goal (representableP 2 (fun (d e :D) => forall g, exists j, g i= d i⊕ j /\ False -> False \/ (e i⊗ iO i= iσ j /\ False))).
  Time representNP.
  Time Qed.
  Goal (representableP 0 (forall a b, a i= b)).
  Time representNP. 
  Time Qed.
  Goal (representableP 0 (forall a b c, a i= b i⊕ c)).
  Time representNP.
  Time Qed.
  Goal (representableP 0 (forall a b c d ,a i= b i⊕ c i⊕ d)).
  Time representNP. 
  Time Qed.
  Goal (representableP 0 (forall a b c d e , a i= b i⊕ c i⊕ d i⊕ e)).
  Time representNP. 
  Time Qed.
  Goal (representableP 0 (forall a b c d e f , a i= b i⊕ c i⊕ d i⊕ e i⊕ f)).
  Time representNP. 
  Time Qed.
  Goal (representableP 0 (forall a b c d e f g , a i= b i⊕ c i⊕ d i⊕ e i⊕ f i⊕ g)).
  Time representNP.
  Time Qed.
  Goal (representableP 2 (fun a b=> a i= b)).
  Time representNP. 
  Time Qed.
  Goal (representableP 3 (fun a b c=> a i= b i⊕ c)).
  Time representNP.
  Time Qed.
  Goal (representableP 4 (fun a b c d =>a i= b i⊕ c i⊕ d)).
  Time representNP. 
  Time Qed.
  Goal (representableP 5 (fun a b c d e => a i= b i⊕ c i⊕ d i⊕ e)).
  Time representNP. 
  Time Qed.
  Goal (representableP 6 (fun a b c d e f => a i= b i⊕ c i⊕ d i⊕ e i⊕ f)).
  Time representNP. 
  Time Qed.
  Goal (representableP 7 (fun a b c d e f g => a i= b i⊕ c i⊕ d i⊕ e i⊕ f i⊕ g)).
  Time representNP.
  Time Qed.

  Goal (forall n:nat, representableP 1 (fun a => a i= iμ n)).
  intros n. Time represent. Show Proof.
  Time Qed.

  Goal forall (d e:D), representableP 0 (d i= e).
  intros d e. representNP.
  Qed.
  Goal forall (d e:D), representableP 0 (d = e <-> True).
  intros d e. represent. Show Proof.
  Qed.
  Goal forall (d e:D), representableP 0 (d i= e <-> False).
  intros d e. representNP. Show Proof. Restart. intros d e. represent. Show Proof.
  Qed.
  Goal forall (d e:D), representableP 0 (d = e <-> True).
  intros d e. representNP. cbv in rep. unfold HiddenTerm, fst in envBase. Show Proof.
  Abort.



  (* provide all axioms in a more useful form *)
  Theorem succ_inj:
    (forall rho, rho ⊨ ax_succ_inj) -> forall n d, iσ d = iσ n -> d = n.
  Proof.
    intros H n d. specialize (H (fun _ => iO) d n).
    cbn in H. rewrite !equality in H; now cbn in H.
  Qed.

  Theorem add_zero :
    (forall rho, rho ⊨ ax_add_zero) -> forall d, iO i⊕ d = d.
  Proof.
    intros H d. specialize (H (fun _ => iO) d).
    cbn in H. rewrite equality in H; now cbn in H.
  Qed.

  Theorem add_rec :
    (forall rho, rho ⊨ ax_add_rec) -> forall n d, (iσ n) i⊕ d = iσ (n i⊕ d). 
  Proof.
    intros H n d.
    specialize (H (fun _ => iO) d n).
    cbn in H. rewrite !equality in H; now cbn in H.
  Qed.
      
  Theorem mult_zero :
    (forall rho, rho ⊨ ax_mult_zero) -> forall d, iO i⊗ d = iO.
  Proof.
    intros H d. specialize (H (fun _ => iO) d).
    cbn in H. rewrite !equality in H. now cbn in H.
  Qed.

  Theorem mult_rec :
    (forall rho, rho ⊨ ax_mult_rec) -> forall n d, (iσ d) i⊗ n = n i⊕ (d i⊗ n).
  Proof.
    intros H n d. specialize (H (fun _ => iO) d n).
    cbn in H. rewrite !equality in H; now cbn in H.
  Qed.

  
  Variable AX : sat_PA_minimal_axioms.
  
  
  Theorem PAinduction_weak (phi : form) rho :
    rho ⊨ phi[zero..] -> rho ⊨ (∀ phi --> phi[σ $ 0 .: S >> var]) -> rho ⊨ (∀ phi).
  Proof.
    destruct (AX rho) as (_&_&_&_&_&H). cbn. apply (H phi).
  Qed.
  
  
  Definition null := (fun _ : nat => iO).
  Notation representable P := (representableP 1 P). (*exists phi rho, forall d, P d <-> (d.:rho) ⊨ phi.*)

  Lemma sat_single (rho : nat -> D) (Phi : form) (t : term) :
    (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
  Proof.
    rewrite sat_comp. apply sat_ext. now intros [].
  Qed.

  (** Useful induction principle *)
  
  Theorem PAinduction (P : D -> Prop) :
    representable P -> P iO -> (forall d, P d -> P (iσ d)) -> forall d, P d.
  Proof.
    intros (phi & rho & repr) P0 IH. intros d. unfold representsP in repr. rewrite repr.
    apply PAinduction_weak.
    - apply sat_single. apply repr. apply P0.
    - cbn. intros d' H. apply repr, IH, repr in H.
      apply sat_comp. eapply sat_ext; try apply H. now intros [].
  Qed.

  (** Examples *)

  Lemma add_exists : forall (phi : form) rho, rho ⊨ phi -> exists sigma, sigma ⊨ (∃ phi).
  Proof.
    intros phi rho H; cbn. exists (fun n => match n with
                           | O => rho 1
                           | S m => rho (S n)
                                end); exists (rho 0).
    unfold scons. eapply sat_ext; try apply H. now intros [|[|]].
  Qed.

  Definition exist_times n (phi : form) := iter (fun psi => ∃ psi) n phi.
  
  Lemma add_n_exists : forall n,
      forall (phi : form) rho, rho ⊨ phi -> exists sigma, sigma ⊨ (exist_times n phi).
  Proof.
    induction n; intros phi rho H.
    - exists rho. auto. 
    - destruct (IHn _ _ H) as [s Hs]. now refine (add_exists _ s _).
  Qed.
  
  Lemma zero_or_succ : forall rho, rho ⊨ (∀ zero == $0 ∨ ∃ $1 == σ $0).
  Proof.
    intros rho. apply PAinduction_weak.
    - left. now apply equality.
    - intros d _. right. exists d; now apply equality.
  Qed.


  Goal forall d, iO = d \/ exists x, d = iσ x. 
  Proof.
    enough (forall rho, rho ⊨ (∀ zero == $0 ∨ ∃ $1 == σ $0)) as H. intros d.
    specialize (H null). cbn in H. specialize (H d). revert H.
    rewrite equality. cbn.
    intros [<- | [x H]]. now left. right. rewrite equality in H. now exists x.
    apply zero_or_succ.
  Qed.

  Goal forall d, iO = d \/ exists x, d = iσ x. 
  Proof.
    apply PAinduction. represent.
    - now left.
    - intros d [<- |]; right. now exists iO. now exists d.
  Qed.

  Lemma add_rec_right :
    forall d n, n i⊕ (iσ d) = iσ (n i⊕ d).
  Proof.
    intros n. apply PAinduction.
    - represent. 
    - rewrite !add_zero; try reflexivity. all: firstorder.
    - intros d IH. rewrite !add_rec. cbn in IH. cbn. now rewrite IH. all: firstorder.
  Qed.
    
  
  Section TrivialModel.
    Variable Bot : iμ 0 = iμ 1.
    
    Lemma ModelHasOnlyZero' rho : rho ⊨ (∀ $0 == zero).
    Proof.
      apply PAinduction_weak.
      - cbn; now apply equality.
      - cbn. fold iO. intros d. rewrite !equality; cbn. intros IH.
        now rewrite IH. 
    Qed.

    
    Fact ModelHasOnlyZero : forall d, d = iO.
    Proof.
      apply PAinduction. 
      - represent.
      - reflexivity.
      - intros d. now intros ->.
    Qed.

    
    Lemma trivial_induction' rho phi : rho ⊨ (phi[zero..] --> ∀ phi).
    Proof.
      cbn. intros H0. apply PAinduction_weak.
      - exact H0.
      - cbn. intros d IH. apply sat_comp.
        refine (@sat_ext' _ _ _ _ (d.:rho) _ phi _ _).
        destruct x; cbn; rewrite ModelHasOnlyZero; apply ModelHasOnlyZero.
        exact IH.
    Qed.
      
    
    Fact trivial_induction : forall P, representable P -> P iO -> forall d, P d.
    Proof.
      intros P Rep P0. apply PAinduction; try auto.
      intros. now rewrite ModelHasOnlyZero.  
    Qed.
    
         
  End TrivialModel.
 
End Models.











(*** Working with a Deduction System ***)

Section ND.

  Variable p : peirce.
  Definition FA' := ax_add_zero::ax_add_rec::ax_mult_zero::ax_mult_rec::nil.

  Definition ax_refl := (∀ $0 == $0).
  Definition ax_sym := (∀ ∀ $0 == $1 --> $1 == $0).
  Definition ax_trans := (∀∀∀ $0 == $1 --> $1 == $2 --> $0 == $2).

  Definition ax_eq_succ := (∀∀ $0 == $1 --> σ $0 == σ $1).
  Definition ax_eq_add := (∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊕ $2 == $1 ⊕ $3).
  Definition ax_eq_mult := (∀∀∀∀ $0 == $1 --> $2 == $3 --> $0 ⊗ $2 == $1 ⊗ $3).

  Definition FA := ax_refl::ax_sym::ax_trans::ax_eq_succ::ax_eq_add::ax_eq_mult::FA'.

  Lemma numeral_subst_invariance : forall n rho, subst_term rho (num n) = num n.
  Proof.
    induction n.
    - reflexivity.
    - intros rho. cbn. now rewrite IHn.
  Qed.

  Lemma term_subst_invariance t : forall rho,
      bound_term 0 t = true -> subst_term rho t = t.
  Proof.
    induction t.
    - intros ? H. inversion H.
    - intros rho HB. cbn. f_equal.
      enough ( Vector.map (subst_term rho) v = Vector.map id v ) as eq.
      cbn in eq. rewrite eq at 1. now rewrite (Vector.map_id _ _).
      apply Vector.map_ext_in.
      intros x Hx. cbv [id]. apply IH.
      assumption. refine (bound_term_parts _ _).
      apply HB. now apply vec_map_In.
  Qed.

  Lemma FA_refl t :
    FA ⊢ (t == t).
  Proof.
    assert (FA ⊢ ax_refl). apply Ctx. firstorder.
    eapply AllE in H. cbn in H. apply H.
  Qed.

  Lemma FA_sym t t' :
    FA ⊢ (t == t') -> FA ⊢ (t' == t).
  Proof.
    intros H. assert (H' : FA ⊢ ax_sym). apply Ctx. firstorder.
    eapply (AllE _ t') in H'. cbn in H'. apply (AllE _ t) in H'. cbn in H'.
    change (FA ⊢ (t == t'[↑][t..] --> t'[↑][t..] == t)) in H'.
    rewrite subst_term_shift in H'. apply (IE _ _ _ H'), H.
  Qed.
  
  Lemma num_add_homomorphism x y :
    FA ⊢ (num x ⊕ num y == num (x + y)).
  Proof.
  Admitted.

  Lemma num_mult_homomorphism x y : FA ⊢ ( num x ⊗ num y == num (x * y) ).
  Proof.
  Admitted.

  Lemma lebiniz phi t t' :
    FA ⊢ (t == t') -> FA ⊢ phi[t..] -> FA ⊢ phi[t'..].
  Proof.
  Admitted.

End ND.

Locate ";".
