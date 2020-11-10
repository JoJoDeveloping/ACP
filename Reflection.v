From MetaCoq.Template Require Import utils All Pretty.
Print term.
Locate term.
Require Import List String.
Import MonadNotation.

Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import VectorTech.
Require Import Lia.


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

Definition zero := func Zero (Vector.nil term).
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

  Variable D : Type.
  Context {I : interp D}.

  Definition Equality := forall v, @i_P _ _ D I Eq v <-> Vector.hd v = Vector.hd (Vector.tl v). 
  Hypothesis equality : forall v, @i_P _ _ D I Eq v <-> Vector.hd v = Vector.hd (Vector.tl v).

  Notation "'iO'" := (i_f (f:=Zero) (Vector.nil D)).
  Notation "'iσ' d" := (i_f (f:=Succ) (Vector.cons d (Vector.nil D))) (at level 37).
  Notation "x 'i⊕' y" := (i_f (f:=Plus) (Vector.cons x (Vector.cons y (Vector.nil D)))) (at level 39).
  Notation "x 'i⊗' y" := (i_f (f:=Mult) (Vector.cons x (Vector.cons y (Vector.nil D)))) (at level 38).
  Notation "x 'i=' y" := (i_P (P:=Eq)   (Vector.cons x (Vector.cons y (Vector.nil D)))) (at level 40).
  Definition iμ k := iter (fun x => iσ x) k iO.
  Fixpoint naryProp (n:nat) : Type := match n with 0 => Prop | S nn => D -> naryProp nn end.
  Fixpoint representsP {n:nat} phi rho : (forall (P:naryProp n), Prop) := match n return (forall (P:naryProp n), Prop) with
       0  => (fun (P:Prop) => P <-> rho ⊨ phi)
    | S n => (fun (P:D -> naryProp n) => forall d, @representsP n phi (d.:rho) (P d)) end.
  Definition representableP (n:nat) (P : naryProp n) := exists phi rho, representsP phi rho P.
  Definition representsF (d:D) trm rho := eval rho trm = d.
  Definition representableF (d:D) := exists trm rho, representsF d trm rho.


Notation quoteO := (tApp (tConst (MPfile (["Tarski"; "Arith"]), "i_f") nil)
   ([tConst (MPfile (["Reflection"; "Arith"]), "PA_funcs_signature") (nil);
   tConst (MPfile (["Reflection"; "Arith"]), "PA_preds_signature") nil;
   tVar "D"; tVar "I";
   tConstruct
     {|
     inductive_mind := (MPfile (["Reflection"; "Arith"]), "PA_funcs");
     inductive_ind := 0 |} 0 nil;
   tApp
     (tConstruct
        {|
        inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t");
        inductive_ind := 0 |} 0 nil) ([tVar "D"])])).
Notation quoteS x := 
(tApp (tConst (MPfile (["Tarski"; "Arith"]), "i_f") nil)
   ([tConst (MPfile (["Reflection"; "Arith"]), "PA_funcs_signature") nil;
   tConst (MPfile (["Reflection"; "Arith"]), "PA_preds_signature") nil;
   tVar "D"; tVar "I";
   tConstruct
     {|
     inductive_mind := (MPfile (["Reflection"; "Arith"]), "PA_funcs");
     inductive_ind := 0 |} 1 nil;
   tApp
     (tConstruct
        {|
        inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t");
        inductive_ind := 0 |} 1 nil)
     ([tVar "D"; x;
     tConstruct
       {|
       inductive_mind := (MPfile (["Datatypes"; "Init"; "Coq"]), "nat");
       inductive_ind := 0 |} 0 nil;
     tApp
       (tConstruct
          {|
          inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t");
          inductive_ind := 0 |} 0 nil) ([tVar "D"])])])).
Notation quoteFalse := 
(tInd
   {|
   inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), "False");
   inductive_ind := 0 |} nil).
Notation quoteAnd x y := 
(tApp
   (tInd
      {|
      inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), "and");
      inductive_ind := 0 |} nil)
   ([x;y])).
Notation quoteForall x P := (tProd (nNamed x) (tVar "D") P).
Notation quoteEq x y :=
(tApp (tConst (MPfile (["Tarski"; "Arith"]), "i_P") nil)
   ([tConst (MPfile (["Reflection"; "Arith"]), "PA_funcs_signature") nil; tConst (MPfile (["Reflection"; "Arith"]), "PA_preds_signature") nil;
   tVar "D"; tVar "I"; tConstruct {| inductive_mind := (MPfile (["Reflection"; "Arith"]), "PA_preds"); inductive_ind := 0 |} 0 nil;
   tApp (tConstruct {| inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t"); inductive_ind := 0 |} 1 nil)
     ([tVar "D"; x;
     tApp (tConstruct {| inductive_mind := (MPfile (["Datatypes"; "Init"; "Coq"]), "nat"); inductive_ind := 0 |} 1 nil)
       ([tConstruct {| inductive_mind := (MPfile (["Datatypes"; "Init"; "Coq"]), "nat"); inductive_ind := 0 |} 0 nil]);
     tApp (tConstruct {| inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t"); inductive_ind := 0 |} 1 nil)
       ([tVar "D"; y; tConstruct {| inductive_mind := (MPfile (["Datatypes"; "Init"; "Coq"]), "nat"); inductive_ind := 0 |} 0 nil;
       tApp (tConstruct {| inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t"); inductive_ind := 0 |} 0 nil) ([tVar "D"])])])])).
Notation quoteLambda x P := (tLambda (nNamed x) (tVar "D") P).
Definition failEnv (n:nat) : (TemplateMonad term):= tmFail ("Unbound " ++ string_of_nat n).
Definition relLift (k : TemplateMonad term) : (TemplateMonad term) := kv <- k ;; match kv with var n => ret (var (S n)) | v => ret v end.
Definition appendZero (k:TemplateMonad term) (v:nat -> TemplateMonad term) (n:nat) := match n with 0 => k | S n => v n end.
Definition appendAndLift (k:TemplateMonad term) (v:nat -> TemplateMonad term) := appendZero k (v >> relLift).


Fixpoint findTermRepresentation (t:Ast.term) (env:nat->TemplateMonad term) {struct t}: (TemplateMonad term) := let fail :=tmPrint t;;tmFail ("Cannot represent term") in match t with
  quoteO => ret zero
| quoteS v => 
      st <- findTermRepresentation v env;;
      ret (σ st)
| tRel k => env k
| _ => fail
end.

Fixpoint findPropRepresentation (t:Ast.term) (frees:nat) (env:nat->TemplateMonad term) {struct t}: (TemplateMonad (form)) := let fail :=tmPrint (frees,t);;tmFail ("Cannot represent form") in 
  match (frees,t) with
  (0,quoteFalse) => ret (fal)
| (0,quoteAnd x y) => 
      xr <- findPropRepresentation x 0 env;;
      yr <- findPropRepresentation y 0 env;;
      ret ((xr ∧ yr))
| (0,quoteForall x P) =>
      rv <- findPropRepresentation P 0 (appendAndLift (ret (var 0)) env);;
      ret ((∀ rv))
| (o,tProd _ P Q) =>
      rP <- findPropRepresentation P 0 env;;
      rQ <- findPropRepresentation Q 0 (appendZero (tmFail "Used var of implication precondition") env);;
      ret (rP --> rQ)
| (0,quoteEq tl tr) =>
      tlr <- findTermRepresentation tl env;;
      trr <- findTermRepresentation tr env;;
      ret ((tlr == trr))
| (S n,quoteLambda x P) => 
      rv <- findPropRepresentation P n (appendAndLift (ret (var 0)) env);;
      ret (rv)
| _ => fail
end.

(*MetaCoq  Run (a <- tmQuote (iσ (iσ iO));; k <- findTermRepresentation a;; tmDefinition "res" k).*)
(*MetaCoq  Run (a <- tmQuote (forall (x:D), x i= x);; k <- findPropRepresentation a failEnv;; tmPrint k).*)


Ltac represent:= match goal with [ |- representableP ?n ?G ] =>
  let fr := fresh "rep" in let kkk := fresh "sml" in let pr := fresh "denv" in let k y := (pose y as fr) in
  (run_template_program (g <- (tmQuote G);;findPropRepresentation g n failEnv) k)
  ;exists fr; pose (fun (_:nat) => iO) as pr; exists pr; split; easy
  end.

Goal (representableP 0 False).
Proof. 
represent.
Qed.

Goal (representableP 0 (False /\ False -> False)).
Proof. 
represent.
Qed.

Goal (representableP 0 (forall d, False -> iσ d i= iO)).
Proof. 
represent. 
Qed.

Goal (representableP 2 (fun (d e:D) => forall g, g i= d)).
Proof. 
represent.
Qed.

Check well_founded_induction.
Check List.Forall.
Structure matchEnviron : Type := {
target : Type;
subterm : target -> target -> Prop;
subterm_wf : well_founded subterm;
selector : forall t:target, option {l : list (target) & List.Forall (fun k => subterm k t) l};

}.

Lemma foldingForall (P : Prop) phi rho : @representsP 0 phi rho P -> representableP 0 (forall x:D, P).
intros H. unfold representsP in H. unfold representableP. 
pose (∀ phi) as kk. exists kk. exists rho. split.
* intros Hf d. apply H. now apply Hf.
* intros Hb d. apply H. now apply Hb.
Qed.

Print k.
  Lemma sat_single (rho : nat -> D) (Phi : form) (t : term) :
    (eval rho t .: rho) ⊨ Phi <-> rho ⊨ subst_form (t..) Phi.
  Proof.
    rewrite sat_comp. apply sat_ext. now intros [].
  Qed.

  (** Useful induction principle *)
(* The following predicate expresses that a model satisfies the minimal axioms of PA i.e. all axioms except S x <> 0 *)
  Definition sat_PA_minimal_axioms :=
    forall rho,
      rho ⊨ ax_succ_inj
      /\ rho ⊨ ax_add_zero
      /\ rho ⊨ ax_add_rec
      /\ rho ⊨ ax_mult_zero
      /\ rho ⊨ ax_mult_rec
      /\ (forall phi, rho ⊨ (PA_induction phi) ).   
  Variable AX : sat_PA_minimal_axioms.  
  Theorem PAinduction_weak (phi : form) rho :
    rho ⊨ phi[zero..] -> rho ⊨ (∀ phi --> phi[σ $ 0 .: S >> var]) -> rho ⊨ (∀ phi).
  Proof.
    destruct (AX rho) as (_&_&_&_&_&H). cbn. apply (H phi).
  Qed.
  Theorem PAinduction (P : D -> Prop) :
    representable 1 P -> P iO -> (forall d, P d -> P (iσ d)) -> forall d, P d.
    intros (phi & rho & repr) P0 IH. intros d. unfold represents in repr. rewrite repr.
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
    apply PAinduction.
    pose (phi := zero == $0 ∨ ∃ $1 == σ $0).
    - exists phi, (fun _ => iO). split.
      + intros [<- | [x ->]].
        * left. cbn. now rewrite equality.
        * right. exists x. cbn. now rewrite equality.
      + intros [H | [x H]].
        * left. cbn in H. now rewrite equality in H.
        * right. exists x. cbn in H. now rewrite equality in H.
    - now left.
    - intros d [<- |]; right. now exists iO. now exists d.
  Qed.

  Lemma add_rec_right :
    forall d n, n i⊕ (iσ d) = iσ (n i⊕ d).
  Proof.
    intros n. apply PAinduction.
    - pose (phi := ∀ $1 ⊕ σ $2 == σ ($1 ⊕ $2) ).
      exists phi. exists (fun _ => n). intros d. cbn. split.
      + intros H d0. rewrite equality. cbn. easy.
      + intros H. specialize (H n). rewrite equality in H. cbn in H. auto.
    - rewrite !add_zero; try reflexivity. all: firstorder.
    - intros d IH. rewrite !add_rec. now rewrite IH. all: firstorder.
  Qed.

End Models.