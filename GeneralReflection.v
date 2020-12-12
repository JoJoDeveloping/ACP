Require Import MetaCoq.Checker.Checker.
From MetaCoq.Template Require Import utils All Pretty.
Require Import List String.
Import MonadNotation.
Require Import FOL.
Require Import Deduction.
Require Import Tarski.
Require Import VectorTech.
Require Import Lia.

Section FailureMonad.
  (* Our monad for creating proper error messages. *)
  Inductive FailureMonad (A:Type) : Type := ret : A -> FailureMonad A | fail : string -> FailureMonad A.
  Arguments ret {_} _.
  Arguments fail {_} _.
  Definition bind {A B : Type} (k:FailureMonad A) (f:A -> FailureMonad B) := match k return FailureMonad B with fail x => fail x | ret k => f k end.
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)).
  (* "Converts" from our monad to the TemplateMonad of MetaCoq. This is used to pass error messages back to the user *)
  Definition f2t {T:Type} (a:FailureMonad T) : TemplateMonad T := match a with ret k => monad_utils.ret k | fail s => tmFail s end.
  (* Structurally recursive definition of a monadic map *)
  Fixpoint flatten_monad {A:Type} (l:list (FailureMonad A)) : FailureMonad (list A) := match l with nil => ret nil | x::xr => xm <- x;; xrm <- flatten_monad xr;; ret (xm::xrm) end.
  Definition map_monad {A B:Type} (f:A -> FailureMonad B) (l:list A) : FailureMonad (list B) := flatten_monad (map f l).
  (* If the first monad fails, use the second. Used to cascade failure handling *)
  Definition orelse {A:Type} (F1 F2 :FailureMonad A) := match F1 with fail _ => F2 | _ => F1 end.
End FailureMonad.

Arguments ret {_} _.
Arguments fail {_} _.
Arguments orelse {_} _ _.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)).
Arguments Vector.cons {_} _ {_} _, _ _ _ _.

Section MetaCoqUtils.
  (* Working with quoted vectors *)
  Notation vectorCons x T n xr := 
  (tApp
   (tConstruct
      {|
      inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t");
      inductive_ind := 0 |} 1 nil)
   ([T; x; n; xr])).
  Notation vectorNil T :=
  (tApp
   (tConstruct
      {|
      inductive_mind := (MPfile (["VectorDef"; "Vectors"; "Coq"]), "t");
      inductive_ind := 0 |} 0 nil) ([T])).
  (* Unquotes a vector (into a list) *)
  Fixpoint recoverVector (f : Ast.term) {struct f}: FailureMonad (list Ast.term) := let ffail := fail "not a vector application" in match f with
    vectorNil _ => ret nil
  | vectorCons x _ _ xr => xrl <- recoverVector xr;;ret (x::xrl)
  | _ => ffail
  end.

  (* General utils for quoted terms *)
  (* Remove the n first elements from a list *)
  Existing Instance config.default_checker_flags.
  Fixpoint popNElements (l : list Ast.term) (n:nat) : option (list Ast.term) := match (l,n) with
    (a,0) => Some a
  | (x::xr, S n) => popNElements xr n
  | _ => None end.
  (* If ls is a valid prefix of l, return the corresponding "suffix" (the remaining elements of l). Otherwise, return None *)
  Fixpoint popListStart (l : list Ast.term) (ls : list Ast.term) : option (list Ast.term) := match (l,ls) with
    (a,nil)=> Some a
  | (lx::lxr, lsx::lsxr) => if Checker.eq_term init_graph lx lsx then popListStart lxr lsxr else None
  | _ => None end.
  MetaCoq Quote Definition qNatZero := 0.
  MetaCoq Quote Definition qNatSucc := S.
  MetaCoq Quote Definition qeq_refl := (@eq_refl).
  (* Given n, yield a MetaCoq Ast.term representation of n *)
  Fixpoint quoteNumber (n:nat) : Ast.term:= match n with 0 => qNatZero | S n => tApp qNatSucc ([quoteNumber n]) end.

  (* Increases the indices of all tRel in t by amnt, assuming they are already larger than minn. If minn = 0, this increases all "free" tRel reference indices *)
  Fixpoint addRelIndex (minn:nat) (amnt:nat) (t:Ast.term) : Ast.term := match t with
    tRel n => if Compare_dec.le_gt_dec minn n then tRel (amnt+n) else tRel n
  | tVar k => tVar k
  | tEvar n ls => tEvar n (map (addRelIndex minn amnt) ls)
  | tSort u => tSort u
  | tCast t ck t2 => tCast (addRelIndex minn amnt t) ck (addRelIndex minn amnt t2)
  | tProd n t v => tProd n (addRelIndex minn amnt t) (addRelIndex (S minn) amnt v)
  | tLambda n t v => tLambda n (addRelIndex minn amnt t) (addRelIndex (S minn) amnt v)
  | tLetIn n t v e => tLetIn n (addRelIndex minn amnt t) (addRelIndex minn amnt v) (addRelIndex (S minn) amnt e)
  | tApp f al => tApp (addRelIndex minn amnt f) (map (addRelIndex minn amnt) al)
  | tConst a b => tConst a b
  | tInd i t => tInd i t
  | tConstruct a b c => tConstruct a b c
  | tCase k i r m => tCase k (addRelIndex minn amnt i) (addRelIndex minn amnt r) (map (fun '(a,b) => (a,addRelIndex minn amnt b)) m)
  | tProj p t => tProj p (addRelIndex minn amnt t)
  | tFix mft n => tFix (map (map_def (addRelIndex minn amnt) (addRelIndex (S minn) amnt)) mft) n
  | tCoFix mft n => tCoFix (map (map_def (addRelIndex minn amnt) (addRelIndex (S minn) amnt)) mft) n
  end.
  Definition map_def_monad {A B : Type} (tyf bodyf : A -> FailureMonad B) (d:def A) : FailureMonad (def B) := dtr <- tyf (dbody d);;dbr <- bodyf (dbody d);; 
                                                                                                            ret {| dname := dname d; dtype := dtr; dbody := dbr; rarg := rarg d |}.
  (* Inverse operation to addRelIndex. Can fail, if the term for instance contains a tRel 0, which would need to be lowered to tRel (-1), which does not exist *)
  Fixpoint lowerRelIndex (minn:nat) (tv:FailureMonad Ast.term) (t:Ast.term) {struct t}: FailureMonad Ast.term := match t with
    tRel n => if Compare_dec.le_gt_dec minn n then if Compare_dec.le_gt_dec minn (S n) then ret (tRel (match n with 0 => 0 | S n => n end)) else tv else ret (tRel n)
  | tVar k => ret (tVar k)
  | tEvar n ls => m <- map_monad (lowerRelIndex minn tv) ls;;ret (tEvar n m)
  | tSort u => ret (tSort u)
  | tCast t ck t2 => mt <- (lowerRelIndex minn tv t);;mt2<-(lowerRelIndex minn tv t2);;ret (tCast mt ck mt2)
  | tProd n t v => mt<-(lowerRelIndex minn tv t);;mv<-(lowerRelIndex (S minn) tv v);;ret (tProd n mt mv)
  | tLambda n t v => mt<-(lowerRelIndex minn tv t);;mv<-(lowerRelIndex (S minn) tv v);;ret (tLambda n mt mv)
  | tLetIn n t v e => mt<-(lowerRelIndex minn tv t);;mv<-(lowerRelIndex minn tv v);;me<-(lowerRelIndex (S minn) tv e);;ret (tLetIn n mt mv me)
  | tApp f al => mal<-(map_monad (lowerRelIndex minn tv) al);;ff <- lowerRelIndex minn tv f;;ret (tApp ff mal)
  | tConst a b => ret (tConst a b)
  | tInd i t => ret (tInd i t)
  | tConstruct a b c => ret (tConstruct a b c)
  | tCase k i r m => mi<-(lowerRelIndex minn tv i);;mr<-(lowerRelIndex minn tv r);;mm<-(map_monad (fun '(a,b) => mb <- lowerRelIndex minn tv b;; ret (a,mb)) m);;ret (tCase k mi mr mm)
  | tProj p t => mt<-(lowerRelIndex minn tv t);;ret (tProj p mt)
  | tFix mft n => mmft<-(map_monad (map_def_monad (lowerRelIndex minn tv) (lowerRelIndex (S minn) tv)) mft);;ret (tFix mmft n)
  | tCoFix mft n => mmft<-(map_monad (map_def_monad (lowerRelIndex minn tv) (lowerRelIndex (S minn) tv)) mft);;ret (tCoFix mmft n)
  end.
End MetaCoqUtils.

Section AbstractReflectionDefinitions.
  (* Types used for extension points *)
  Definition proofRT (b:bool) : Type := FailureMonad (if b then prod Ast.term Ast.term else Ast.term).
  Definition helperTermReifierType := (forall b:bool, Ast.term -> Ast.term -> Ast.term -> (Ast.term -> FailureMonad nat) -> proofRT b).
  Definition helperTermVarsType := (Ast.term -> FailureMonad (list Ast.term)).
  Definition helperFormReifierType := (forall b:bool, Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> proofRT b).
  Definition helperFormVarsType := (Ast.term->nat->FailureMonad (list Ast.term)).

  Definition baseConnectiveReifier := forall b:bool, Ast.term -> list Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> helperFormReifierType -> helperTermReifierType -> proofRT b.
  Definition baseConnectiveVars := list Ast.term -> nat -> Ast.term -> helperFormVarsType -> helperTermVarsType -> FailureMonad (list Ast.term).

  Definition termFinderVars := nat -> Ast.term -> helperTermVarsType -> FailureMonad (list Ast.term).
  Definition termFinderReifier := forall b:bool, Ast.term -> nat -> Ast.term -> Ast.term -> (Ast.term -> FailureMonad nat) 
                                  -> helperTermReifierType -> proofRT b.

  Definition propFinderVars := Ast.term -> nat -> Ast.term -> nat -> helperFormVarsType -> helperTermVarsType -> (FailureMonad (list Ast.term)).
  Definition propFinderReifier := forall b:bool, Ast.term -> nat -> Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> helperFormReifierType -> helperTermReifierType -> proofRT b.

  (* When running in no proof mode, extension points still expect proofs. We give this dummy term. If the extension point only uses this to build further proofs, the whole term is discarded in the end *)
  Definition noProofDummy := tVar "NoProofGivenBecauseWeAreInNoProofMode".
  Definition ifProof (k:bool) r := if k then r else noProofDummy.
  (* An instance of this class is required for the reifier to work. From it the basic reification building blocks are derived *)
  Class tarski_reflector := {
    fs : funcs_signature; 
    ps : preds_signature; (* ps and fs give the syntax *)
    D  : Type;
    I  : @interp fs ps D; (* D and I give our model *)
    emptyEnv : nat -> D;  (* We need an "empty" env that returns some default value for our types *)
    isD : Ast.term -> bool;  (* Returns true iff the given term references D used above *)
  }. 
  (* Extension point to extend the libary to more syntactic constructs *)
  Class tarski_reflector_extensions (t:tarski_reflector) := {
    baseLogicConnHelper : option (string -> baseConnectiveReifier); 
    baseLogicVarHelper : option (string -> baseConnectiveVars);     (* for reifying instances of inductive types Coq.Init.Logic.* applied to arguments. Mostly used for reifying eq *)
    termReifierVarHelper : option termFinderVars;    
    termReifierReifyHelper : option termFinderReifier;              (* for reifying all terms that we fail to reify *)
    formReifierVarHelper : option propFinderVars;
    formReifierReifyHelper : option propFinderReifier               (* for reifying all forms that we fail to reify *)
  }.
  (* Used if no instance of the above extension class can be found *)
  Definition defaultExtensions tr : tarski_reflector_extensions tr := Build_tarski_reflector_extensions tr None None None None None None.
  (* Useful builder to build the main tarski_reflector class *)
  Definition buildDefaultTarski {fs:funcs_signature} {ps:preds_signature} {D:Type} {I:@interp fs ps D} (point:D) (isD:Ast.term -> bool) := Build_tarski_reflector fs ps D I (fun n:nat => point) isD.
  Context {tr : tarski_reflector}.
  (* These types are used to define representability. A n-ary formula is representable if there is a syntactic formula and an environment that you can plug the relevant values into that is equivalent *)
  Fixpoint naryProp (n:nat) : Type := match n with 0 => Prop | S nn => D -> naryProp nn end.
  Fixpoint representsP {n:nat} phi rho : (forall (P:naryProp n), Prop) := match n return (forall (P:naryProp n), Prop) with
       0  => (fun (P:Prop) => P <-> @sat fs ps D I rho phi)
    | S n => (fun (P:D -> naryProp n) => forall d, @representsP n phi (d.:rho) (P d)) end.
  Definition representableP (n:nat) (P : naryProp n) := exists phi rho, representsP phi rho P.
  Definition representsF (d:D) trm rho := @eval fs ps D I rho trm = d.
  Definition representableF (d:D) := exists trm rho, representsF d trm rho.

  (* Functions that allow us to construct syntactic connective applications without building vectors in MetaCoq *)
  Fixpoint naryGFunc (n:nat) (A R : Type) := match n with 0 => R | S n => A -> @naryGFunc n A R end.
  Fixpoint takeMultiple {n : nat} (X Y:Type)  : (Vector.t X n -> Y) -> @naryGFunc n X Y := 
     match n as nn return (Vector.t X nn -> Y) -> @naryGFunc nn X Y
             with 0 => fun R => R (Vector.nil X) 
              | S n => fun R v => @takeMultiple n X Y (fun vr => R (Vector.cons X v n vr)) end.
  Definition constructTerm (k:@syms (@fs tr)) := @takeMultiple (ar_syms k) term term (func k).
  Definition constructForm (k:(@preds (@ps tr))) := @takeMultiple (@ar_preds (@ps tr) k) (@term (@fs tr)) form (atom k).

  Fixpoint nary3GFunc (n:nat) (A B A' B':Type) (C:A -> B -> Type) (C':A'->B'->Type) : (Vector.t A n -> A') -> (Vector.t B n -> B') -> Type
                      := match n with 0 => fun mA mB => C' (mA (Vector.nil A)) (mB (Vector.nil B))
                                  | S n => fun mA mB => forall (a:A) (b:B), C a b -> @nary3GFunc n A B A' B' C C' (fun v => mA (Vector.cons A a n v)) (fun v => mB (Vector.cons B b n v)) end.

  (* Proof that the functions build using the above helper actually represent the syntactic construct they are supposed to represent *)
  Definition mergeTermBase (c:@syms (@fs tr)) : Type := 
  forall (rho:nat -> D), @nary3GFunc (ar_syms c) term D term D 
                                     (fun t d => representsF d t rho) (fun t d => representsF d t rho) 
                                     (func c) (@i_f fs ps D I c).
  Definition mergeTermProtoType (rho:nat -> D) (n:nat) (fZ:vec term n -> term) (ifZ : vec D n -> D) := 
         (forall v : vec term n, @eval fs ps D I rho (fZ v) = ifZ (Vector.map (@eval fs ps D I rho) v))  
         -> @nary3GFunc n term D term D (fun t d => representsF d t rho) (fun t d => representsF d t rho) fZ ifZ.
  Definition mergeTermProto (rho:nat -> D) (n:nat) (fZ:vec term n -> term) (ifZ : vec D n -> D) : mergeTermProtoType rho n fZ ifZ.
  Proof.
  intros H. induction n as [|n IH].
  * cbn. unfold representsF. rewrite H. cbn. easy.
  * cbn. intros t d r. apply IH. cbn. intros v. specialize (H (Vector.cons t v)). unfold representsF in r. rewrite H. cbn. now rewrite r.
  Defined.
  Definition mergeTerm (c:syms) : mergeTermBase c.
  Proof. intros rho. eapply mergeTermProto. now intros v. Defined.

  Definition mergeFormBase (c:@preds (@ps tr)) : Type := 
  forall (rho:nat -> D), @nary3GFunc (ar_preds c) term D form (naryProp 0) 
                                     (fun t d => representsF d t rho) (fun t P => representsP t rho P) 
                                     (atom c) (@i_P fs ps D I c).
  Definition mergeFormProtoType (rho:nat -> D) (n:nat) (fZ:vec term n -> form) (ifZ : vec D n -> naryProp 0) := 
         (forall v : vec term n, @sat fs ps D I rho (fZ v) = ifZ (Vector.map (@eval fs ps D I rho) v))  
         -> @nary3GFunc n term D form (naryProp 0) (fun t d => representsF d t rho) (fun t P => representsP t rho P) fZ ifZ.
  Definition mergeFormProto (rho:nat -> D) (n:nat) (fZ:vec term n -> form) (ifZ : vec D n -> naryProp 0) : mergeFormProtoType rho n fZ ifZ.
  Proof.
  intros H. induction n as [|n IH].
  * cbn. unfold representsP. rewrite H. cbn. easy.
  * cbn. intros t d r. apply IH. cbn. intros v. specialize (H (Vector.cons t v)). unfold representsF in r. rewrite H. cbn. now rewrite r.
  Defined.
  Definition mergeForm (c:preds) : mergeFormBase c.
  Proof. intros rho. eapply mergeFormProto. now intros v. Defined.
  (* Quotes of these functions which are later used to construct (proof) terms *)
  MetaCoq Quote Definition qConstructTerm := constructTerm.
  MetaCoq Quote Definition qMergeTerm := mergeTerm.
  MetaCoq Quote Definition qConstructForm := constructForm.
  MetaCoq Quote Definition qMergeForm := mergeForm.
End AbstractReflectionDefinitions.

Section TarskiMerging.
  (* Code to merge the basic tarski semantics that is fixed for all models - namely logical and, or, implication, falsity, forall and exists-quantisation *)
  Context {tr : tarski_reflector}.
  Context {te : tarski_reflector_extensions tr}.
  Definition mergeFalse (rho:nat -> D) : @representsP tr 0 fal rho False.
  Proof. easy. Defined.
  MetaCoq Quote Definition qMergeFalse := @mergeFalse.
  Definition mFalse := (@fal fs ps full_operators).
  MetaCoq Quote Definition qMergeFormFalse := @mFalse.

  Definition mergeAnd (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form) : representsP fP rho P -> representsP fQ rho Q -> @representsP tr 0 (fP∧fQ) rho (P /\ Q).
  Proof.
  intros [pPl pPr] [pQl pQr]. split.
  * intros [pP pQ]. split. now apply pPl. now apply pQl.
  * intros [pP pQ]. split. now apply pPr. now apply pQr.
  Defined.
  MetaCoq Quote Definition qMergeAnd := @mergeAnd.
  Definition mAnd := (@bin fs ps full_operators Conj).
  MetaCoq Quote Definition qMergeFormAnd := @mAnd.

  Definition mergeOr (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form) : representsP fP rho P -> representsP fQ rho Q -> @representsP tr 0 (fP∨fQ) rho (P \/ Q).
  Proof.
  intros [pPl pPr] [pQl pQr]. split.
  * intros [pP|pQ]. left; now apply pPl. right; now apply pQl.
  * intros [pP|pQ]. left; now apply pPr. right; now apply pQr.
  Defined.
  MetaCoq Quote Definition qMergeOr := @mergeOr.
  Definition mOr := (@bin fs ps full_operators Disj).
  MetaCoq Quote Definition qMergeFormOr := @mOr.

  Definition mergeExists (rho:nat -> D) (P:naryProp 1) (fP:form) : representsP fP rho P -> @representsP tr 0 (∃ fP) rho (exists q:D, P q).
  Proof.
  intros pR. split.
  * intros [q Pq]. exists q. destruct (pR q) as [pRl pRr]. now apply pRl.
  * intros [q Pq]. exists q. destruct (pR q) as [pRl pRr]. now apply pRr.
  Defined.
  MetaCoq Quote Definition qMergeExists := @mergeExists.
  Definition mExists := (@quant fs ps full_operators Ex).
  MetaCoq Quote Definition qMergeFormExists := @mExists.

  Definition mergeImpl (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form) : representsP fP rho P -> representsP fQ rho Q -> @representsP tr 0 (fP --> fQ) rho (P -> Q).
  Proof.
  intros HP HQ.
  destruct HP as [pPl pPr]. destruct HQ as [pQl pQr]. split.
  * intros PQ pP. apply pQl, PQ, pPr, pP.
  * cbn. intros pPQ pP. apply pQr, pPQ, pPl, pP.
  Defined.
  MetaCoq Quote Definition qMergeImpl := @mergeImpl.
  Definition mImpl := (@bin fs ps full_operators Impl).
  MetaCoq Quote Definition qMergeFormImpl := @mImpl.

  Definition mergeForall (rho:nat -> D) (Q:naryProp 1) (phi:form) : representsP phi rho Q -> @representsP tr 0 (∀ phi) rho (forall x:D, Q x).
  Proof. intros H. cbn. split;
   intros HH d; specialize (HH d); specialize (H d); cbn in H; apply H, HH.
  Defined.
  MetaCoq Quote Definition qMergeForall := @mergeForall.
  Definition mForall := (@quant fs ps full_operators All).
  MetaCoq Quote Definition qMergeFormForall := @mForall.

  Definition mergeIff (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form) : representsP fP rho P -> representsP fQ rho Q -> @representsP _ 0 ((fP-->fQ)∧(fQ-->fP)) rho (P <-> Q).
  Proof. intros H1 H2. cbn. cbn in H1,H2. rewrite H2, H1. reflexivity. Defined.
  Definition mIff := (fun fP fQ : form => mAnd (mImpl fP fQ) (mImpl fQ fP)).
  MetaCoq Quote Definition qMergeFormIff := @mIff.
  MetaCoq Quote Definition qMergeIff := mergeIff. 

  Definition mergeTrue (rho:nat -> D) : @representsP _ 0 (fal-->fal) rho (True).
  Proof. cbn. tauto. Defined.
  Definition mTrue := (mImpl mFalse mFalse).
  MetaCoq Quote Definition qMergeFormTrue := @mTrue.
  MetaCoq Quote Definition qMergeTrue := mergeTrue.

  Definition ipT (b:bool) := if b then prod Ast.term Ast.term else Ast.term.
  Definition mergeNone (b:bool) (tct envTerm mergeForm mergeProof : Ast.term) : ipT b := 
          match b return (ipT b) 
         with false => (tApp mergeForm ([tct])) 
            | true => (tApp mergeForm ([tct]), tApp mergeProof ([tct;envTerm])) end.
  Definition mergeOne (b:bool) (tct envTerm mergeForm mergeProof f : Ast.term) : (ipT b -> ipT b) := 
          match b return (ipT b -> ipT b) 
         with false => fun sub =>(tApp mergeForm ([tct;sub])) 
            | true => fun '(t,p) => (tApp mergeForm ([tct;t]), tApp mergeProof ([tct;envTerm;f;t;p])) end.
  Definition mergeTwo (b:bool) (tct envTerm mergeForm mergeProof fx fy : Ast.term) : (ipT b -> ipT b -> ipT b) := 
          match b return (ipT b -> ipT b -> ipT b) 
         with false => fun tx ty =>(tApp mergeForm ([tct;tx;ty])) 
            | true => fun '(tx,px) '(ty,py) => (tApp mergeForm ([tct;tx;ty]), tApp mergeProof ([tct;envTerm;fx;fy;tx;ty;px;py])) end.
  (* Notation for matching constructs like Coq.Init.Logic.and prop1 prop2 -> (x:="and", l:=[term1, term2]) *)
  Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
  Definition reifyFalse : baseConnectiveReifier := fun proof tct lst _ envTerm env fPR _ => match lst with nil => 
                                     ret (mergeNone proof tct envTerm qMergeFormFalse qMergeFalse) | _ => fail "False applied to terms" end. 
  Definition reifyAnd : baseConnectiveReifier := fun proof tct lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xr <- fPR proof x 0 envTerm env;;yr <- fPR proof y 0 envTerm env;; 
                                             ret (mergeTwo proof tct envTerm qMergeFormAnd qMergeAnd x y xr yr) | _ => fail "And applied to != 2 terms" end.
  Definition reifyOr  : baseConnectiveReifier := fun proof tct lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xr <- fPR proof  x 0 envTerm env;;yr <- fPR proof  y 0 envTerm env;;
                                             ret (mergeTwo proof tct envTerm qMergeFormOr qMergeOr x y xr yr) | _ => fail "Or applied to != 2 terms" end.
  Definition reifyExist:baseConnectiveReifier := fun proof tct lst _ envTerm env fPR _ => match lst with [_; P] => 
                                             rr <- fPR proof  P 1 envTerm env;;
                                             ret (mergeOne proof tct envTerm qMergeFormExists qMergeExists P rr) | _ => fail "Exist applied to wrong terms" end.
  Definition reifyIff : baseConnectiveReifier := fun proof tct lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xr <- fPR proof  x 0 envTerm env;;yr <- fPR proof  y 0 envTerm env;;
                                             ret (mergeTwo proof tct envTerm qMergeFormIff qMergeIff x y xr yr) | _ => fail "Iff applied to != 2 terms" end.
  Definition reifyTrue : baseConnectiveReifier := fun proof tct l fuel envTerm env fPR _ => match l with nil =>
                                             ret (mergeNone proof tct envTerm qMergeFormTrue qMergeTrue)| _ => fail "True applied to terms" end.
  Definition reifyBase (s:string): baseConnectiveReifier 
                            := match s with "and" => reifyAnd | "or" => reifyOr | "ex" => reifyExist |  "False" => reifyFalse | "True" => reifyTrue |
                                       _ => match baseLogicConnHelper with 
                                             None =>fun _ _ _ _ _ _ _ _ => fail ("Unknown connective "++s) | 
                                             Some k => k s end end.
  (* Used in no-proof mode, where we just build the representing term and hope they are computationally equal *)
  Definition baseConnectiveReifierNP := Ast.term -> list Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> 
                                       (Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad ( Ast.term)) -> 
                                       (Ast.term -> Ast.term -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad (Ast.term)) -> FailureMonad (Ast.term).
  Definition reifyFalseNP : baseConnectiveReifierNP := fun tct lst _ envTerm env fPR _ => match lst with nil => ret (tApp qMergeFormFalse ([tct])) | _ => fail "False applied to terms" end. 
  Definition reifyAndNP : baseConnectiveReifierNP := fun tct lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xt <- fPR x 0 envTerm env;;yt <- fPR y 0 envTerm env;; 
                                             ret (tApp qMergeFormAnd ([tct;xt;yt])) | _ => fail "And applied to != 2 terms" end.
  Definition reifyOrNP  : baseConnectiveReifierNP := fun tct lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xt <- fPR x 0 envTerm env;;yt <- fPR y 0 envTerm env;; 
                                             ret (tApp qMergeFormOr ([tct;xt;yt])) | _ => fail "Or applied to != 2 terms" end.
  Definition reifyExistNP:baseConnectiveReifierNP := fun tct lst _ envTerm env fPR _ => match lst with [_; P] => 
                                             rt <- fPR P 1 envTerm env;;
                                             ret (tApp qMergeFormExists ([tct;rt])) | _ => fail "Exist applied to wrong terms" end.
  Definition reifyIffNP : baseConnectiveReifierNP := fun tct lst _ envTerm env fPR _ => match lst with [x; y] => 
                                             xt <- fPR x 0 envTerm env;;yt <- fPR y 0 envTerm env;;
                                             ret (tApp qMergeFormIff ([tct;xt;yt])) | _ => fail "Iff applied to != 2 terms" end.
  Definition reifyTrueNP : baseConnectiveReifierNP := fun tct l fuel envTerm env fPR _ => match l with nil =>
                                             ret (tApp qMergeFormTrue ([tct]))| _ => fail "True applied to terms" end.
  Definition reifyBaseNP (s:string): baseConnectiveReifierNP 
                            := match s with "and" => reifyAndNP | "or" => reifyOrNP | "ex" => reifyExistNP |  "False" => reifyFalseNP |  "True" => reifyTrueNP | 
                                       _ => match baseLogicConnHelper with 
                                             None =>fun _ _ _ _ _ _ _ => fail ("Unknown connective "++s) | 
                                             Some k => fun tct lst fuel envTerm env fPR fTR => both <- k s false tct lst fuel envTerm env 
                                                                                                        (fun pr P n et e => rr <- fPR P n et e;; match pr return proofRT pr with true=> ret (rr, noProofDummy) | false=> ret (rr) end) 
                                                                                                        (fun pr tct t eT env => rr <- fTR tct t eT env;; match pr return proofRT pr with true=> ret (rr, noProofDummy) | false=> ret (rr) end);; 
                                                                  ret both end end.

  Definition mergeNoneE (b:bool) (envTerm mergeForm mergeProof : Ast.term) : ipT b := 
          match b return (ipT b) 
         with false => (mergeForm)
            | true => (mergeForm, tApp mergeProof ([envTerm])) end.
  Definition mergeOneE (b:bool) (envTerm mergeForm mergeProof f : Ast.term) : (ipT b -> ipT b) := 
          match b return (ipT b -> ipT b) 
         with false => fun sub =>(tApp mergeForm ([sub])) 
            | true => fun '(t,p) => (tApp mergeForm ([t]), tApp mergeProof ([envTerm;f;t;p])) end.
  Definition mergeTwoE (b:bool) (envTerm mergeForm mergeProof fx fy : Ast.term) : (ipT b -> ipT b -> ipT b) := 
          match b return (ipT b -> ipT b -> ipT b) 
         with false => fun tx ty =>(tApp mergeForm ([tx;ty])) 
            | true => fun '(tx,px) '(ty,py) => (tApp mergeForm ([tx;ty]), tApp mergeProof ([envTerm;fx;fy;tx;ty;px;py])) end.
End TarskiMerging.

Section ReificationHelpers.
  (* Construct the reification (and potentially the proof) of the connectives being used on points of D *)
  Definition termReifier := forall b:bool, Ast.term -> list Ast.term -> Ast.term -> (Ast.term -> proofRT b) -> proofRT b.
  Definition termReifierNP := Ast.term -> list Ast.term -> Ast.term -> (Ast.term -> FailureMonad (Ast.term)) -> FailureMonad (Ast.term).
  (* typeClassTerm -> vector of args -> env term -> recursion for arg vector -> prod (term, proof that term represents input *)
  Fixpoint applyRecursively (lt : list Ast.term) (IH : Ast.term -> FailureMonad (prod Ast.term Ast.term)) : FailureMonad (prod (list Ast.term) (list Ast.term)) :=
     match lt with nil => ret (nil,nil)
               | t::tr => IHt <- IH t;; atrIH <- applyRecursively tr IH;;let '(rep,prf) := IHt in let '(replist,fulllist) := atrIH in ret (rep::replist, rep::t::prf::fulllist) end.
  Fixpoint applyRecursivelyNP (lt : list Ast.term) (IH : Ast.term -> FailureMonad (Ast.term)) : FailureMonad ((list Ast.term) ) :=
     match lt with nil => ret (nil)
               | t::tr => rep <- IH t;; replist <- applyRecursivelyNP tr IH;;ret (rep::replist) end.
  Definition reifyTerm (c:Ast.term) : termReifier := fun proof tct av env => match proof return (Ast.term -> proofRT proof) -> proofRT proof with
                                                      true => fun IH => pr <- applyRecursively av IH;; let '(trm,fullarg) := pr in
                                                       ret (tApp qConstructTerm (tct::c::trm), tApp qMergeTerm (tct::c::env::fullarg))
                                                    | false => fun IH => trm <- applyRecursivelyNP av IH;; ret (tApp qConstructTerm (tct::c::trm)) end.
  Definition reifyForm (c:Ast.term) : termReifier := fun proof tct av env => match proof return (Ast.term -> proofRT proof) -> proofRT proof with
                                                      true => fun IH => pr <- applyRecursively av IH;; let '(trm,fullarg) := pr in
                                                       ret (tApp qConstructForm (tct::c::trm), tApp qMergeForm (tct::c::env::fullarg))
                                                    | false => fun IH => trm <- applyRecursivelyNP av IH;; ret (tApp qConstructForm (tct::c::trm)) end.
  Definition reifyTermNP (c:Ast.term) : termReifierNP := fun tct av env IH => trm <- applyRecursivelyNP av IH;; 
                                                     ret (tApp qConstructTerm (tct::c::trm)).
  Definition reifyFormNP (c:Ast.term) : termReifierNP := fun tct av env IH => trm <- applyRecursivelyNP av IH;; 
                                                     ret (tApp qConstructForm (tct::c::trm)).
End ReificationHelpers.

Section EnvHelpers.
  (* Working with the environment. Since it is sometimes pulled into lambda-functions, and contains tRel terms, it has to be correctly inserted into the lower term *)
  Definition appendZero (env:Ast.term -> FailureMonad nat) (zv:FailureMonad nat) : (Ast.term -> FailureMonad nat) := 
        fun (t:Ast.term) => match t with tRel n => (match n with 0 => zv | S n => env (tRel n) end) | _ => k <- lowerRelIndex 0 (fail "tRel 0 used when lowering") t;; (env k) end.
  Definition appendAndLift (env:Ast.term -> FailureMonad nat) (zv:FailureMonad nat) : (Ast.term -> FailureMonad nat) := 
        fun t => match t with tRel n => (match n with 0 => zv | S n => k <- env (tRel n);;ret (S k) end) | _ => k <- lowerRelIndex 0 (fail "tRel 0 used when lowering") t;; v <- env k;;ret (S v) end.
  MetaCoq Quote Definition qD := @D.
  MetaCoq Quote Definition qScons := @scons.
  Definition raiseEnvTerm (tct:Ast.term) (d:Ast.term) (env:Ast.term) : Ast.term := tApp (qScons) ([tApp qD ([tct]);d;env]).
  Definition unboundEnv := (fun a:Ast.term => @fail nat ("unbound " ++ string_of_term a)).
End EnvHelpers.

Section EnvConstructor.
  (* Constructs the environment used to help with free variables in terms *)
  Existing Instance config.default_checker_flags.
  MetaCoq Quote Definition qFs := @fs.
  MetaCoq Quote Definition qLocalVar := @var.
  MetaCoq Quote Definition qI_f := @i_f.
  MetaCoq Quote Definition qI_P := @i_P.
  Context {tr : tarski_reflector}.
  Context {te : tarski_reflector_extensions tr}.
  (* Given a term in the semantic, construct an environment that contains all atoms that appear in the term (and are not otherwise representable) *)
  Fixpoint findUBRecursively (lt : list Ast.term) (IH : Ast.term -> FailureMonad (list Ast.term)) : FailureMonad ((list Ast.term) ) :=
       match lt with nil => ret (nil)
                 | t::tr => rep <- IH t;; replist <- findUBRecursively tr IH;;ret (rep++replist) end.
  
  Fixpoint findUnboundVariablesTerm (fuel:nat) (t:Ast.term) {struct fuel}: (FailureMonad (list Ast.term)) := match fuel with 
      0 => fail "Out of fuel" 
      | S fuel => let ffail := orelse (match @termReifierVarHelper _ te with None => fail "Fallthrough" | Some k => k fuel t (findUnboundVariablesTerm fuel) end)
                        (match t with tRel _ => ret nil | _ => ret ([t]) end) in (* tRel are things introduced by forall/exists and so on, which we do not add to the environment *)
          match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;findUBRecursively vr (findUnboundVariablesTerm fuel)
           | _ => ffail end else ffail
        | _ => ffail
      end 
    end.
  (*Our notation from above*)
  Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
  (* Find the unbound variables for our basic forms *)
  Definition findUBFalse  :baseConnectiveVars := fun lst _ _ fPR _ => match lst with nil => 
                                             ret (nil) | _ => fail "False applied to terms" end.
  Definition findUBAnd  :baseConnectiveVars := fun lst _ _ fPR _ => match lst with [x; y] => 
                                             xt <- fPR x 0;;yt <- fPR y 0;; 
                                             ret (xt++yt) | _ => fail "And applied to != 2 terms" end.
  Definition findUBOr   :baseConnectiveVars := fun lst _ _ fPR _ => match lst with [x; y] => 
                                             xt <- fPR x 0;;yt <- fPR y 0;; 
                                             ret (xt++yt) | _ => fail "Or applied to != 2 terms" end.
  Definition findUBExists:baseConnectiveVars := fun lst _ _ fPR _ => match lst with [_; P] => fPR P 1 | _ => fail "Exist applied to wrong terms" end.
  Definition findUBTrue : baseConnectiveVars := fun lst fuel tct _ _ => match lst with nil => ret nil | _ => fail "True applied to terms" end.
  Definition findUBIff  :baseConnectiveVars := fun lst _ _ fPR _ => match lst with [x; y] => 
                                           xt <- fPR x 0;;yt <- fPR y 0;; 
                                           ret (xt++yt) | _ => fail "Iff applied to != 2 terms" end.

  Definition findUBBase (s:string) : baseConnectiveVars 
          := match s with "and" => findUBAnd | "or" => findUBOr | "ex" => findUBExists | "False" => findUBFalse | "True" => findUBFalse | _ => 
                match @baseLogicVarHelper tr te with None => fun _ _ _ _ _ => fail ("Unknown connective "++s) | Some k => k s end end.
  MetaCoq Quote Definition qIff := @iff.
  Definition maybeD : Ast.term -> Ast.term -> bool := fun tct mD => if @isD tr mD then true else Checker.eq_term init_graph mD (tApp qD ([tct])).
  Fixpoint findUnboundVariablesForm (tct:Ast.term) (fuel:nat) (t:Ast.term) (frees:nat) {struct fuel}: (FailureMonad (list Ast.term)) := 
  let ffail := fail ("Cannot introspect form "++ string_of_term t) in match fuel with 0 => fail "Out of fuel" | S fuel => 
    match (frees,t) with
    (0,(baseLogicConn name nil)) => findUBBase name nil fuel tct (findUnboundVariablesForm tct fuel) (findUnboundVariablesTerm fuel)
  | (0,(tApp (baseLogicConn name nil) lst)) => findUBBase name lst fuel tct (findUnboundVariablesForm tct fuel) (findUnboundVariablesTerm fuel)
  | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
          Some ([fnc;v]) => vr <- recoverVector v;;findUBRecursively vr (fun t => findUnboundVariablesTerm fuel t)
        | _ => ffail  end else if Checker.eq_term init_graph arg qIff then findUBIff lst fuel tct (findUnboundVariablesForm tct fuel) (findUnboundVariablesTerm fuel) else ffail 
  | (0,tProd x P Q) => if maybeD tct (P) then
                            findUnboundVariablesForm tct fuel (tLambda x P Q) 1
                       else (*implication*)
                            rP <- findUnboundVariablesForm tct fuel P 0;;
                            Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                            rQ <- findUnboundVariablesForm tct fuel Ql 0;;
                            ret (rP++rQ)
  | (S n,tLambda x T P) => if maybeD tct T then
        findUnboundVariablesForm tct fuel P n
       else ffail
  | _ => ffail  end end.
 (* Builds the actual env out of a list of free variables *)
 Fixpoint createEnvTerms (tct:Ast.term) (l:list Ast.term) (base:Ast.term) : prod (Ast.term) (Ast.term -> FailureMonad nat) := match l with 
       nil => (base,unboundEnv)
   | x::xr => let '(envTerm,env) := createEnvTerms tct xr base in (raiseEnvTerm tct x envTerm, fun a:Ast.term => if Checker.eq_term init_graph x a then ret 0 else v <- env a;;ret (S v)) end.
End EnvConstructor.

Section MainReificationFunctions.
  Context {tr : tarski_reflector}.
  Context {te : tarski_reflector_extensions tr}.
  Existing Instance config.default_checker_flags.
  (* Constructs the actual term representing some term of the model, along with a proof *)
  Fixpoint findTermRepresentation (proof:bool) (tct:Ast.term) (fuel:nat) (t:Ast.term) (termEnv:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (proofRT proof) := match fuel with 
      0 => fail "Out of fuel" 
      | S fuel =>
    let fallback := orelse (match @termReifierReifyHelper _ te with None => fail "none" | Some k => k proof tct fuel t termEnv env (fun p l => findTermRepresentation p l fuel) end)
                           (envv <- env (t);;let num := quoteNumber (envv) in match proof return proofRT proof with true => ret (tApp qLocalVar ([tApp qFs ([tct]);num]),(tApp qeq_refl ([tApp qD ([tct]);t]))) | false => ret (tApp qLocalVar ([tApp qFs ([tct]);num])) end) in match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;reifyTerm fnc proof tct vr termEnv (fun t => findTermRepresentation proof tct fuel t termEnv env)
           | _ => fallback end else fallback
        | _ => fallback
      end 
    end.
  (* Like the above, but without the proof *)
  Fixpoint findTermRepresentationNP (tct:Ast.term) (fuel:nat) (t:Ast.term) (termEnv:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (Ast.term)) := match fuel with 
      0 => fail "Out of fuel" 
      | S fuel =>
    let fallback := orelse (match @termReifierReifyHelper _ te with None => fail "none" | Some k => pr <- k false tct fuel t termEnv env (fun pr tct' t' te' e' => v <- findTermRepresentationNP tct' fuel t' te' e';;match pr return proofRT pr with false=>ret (v)|true => ret(v,noProofDummy) end);; ret pr end)
                           (envv <- env (t);;let num := quoteNumber (envv) in ret (tApp qLocalVar ([tApp qFs ([tct]);num]))) in match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;reifyTermNP fnc tct vr termEnv (fun t => findTermRepresentationNP tct fuel t termEnv env)
           | _ => fallback end else fallback
        | _ => fallback
      end 
    end.

    Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).

    (* Like the above, but here we do it for statements about points of D instead of points of D *)
    Fixpoint findPropRepresentation (proof:bool) (tct:Ast.term) (fuel:nat) (t:Ast.term) (frees:nat) (envTerm:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (proofRT proof) := 
    match fuel with 0 => fail "Out of fuel" | S fuel => 
    let ffail := orelse (match @formReifierReifyHelper _ te with None => fail "none" | Some k => k proof tct fuel t frees envTerm env (fun proof => findPropRepresentation proof tct fuel) (fun p l => findTermRepresentation p l fuel) end) 
                        (fail ("Cannot represent form " ++ string_of_term t)) in match (frees,t) with
      (0,(baseLogicConn name nil)) => reifyBase name proof tct nil fuel envTerm env (fun p => findPropRepresentation p tct fuel) (fun p tct => findTermRepresentation p tct fuel)
    | (0,(tApp (baseLogicConn name nil) lst)) => reifyBase name proof tct lst fuel envTerm env (fun proof=>findPropRepresentation proof tct fuel) (fun p tct => findTermRepresentation p tct fuel)
    | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
            Some ([fnc;v]) => vr <- recoverVector v;;reifyForm fnc proof tct vr envTerm (fun t => findTermRepresentation proof tct fuel t envTerm env)
          | _ => ffail end else if Checker.eq_term init_graph arg qIff then reifyIff proof tct lst fuel envTerm env (fun p => findPropRepresentation p tct fuel) (fun p tct => findTermRepresentation p tct fuel) else ffail
    | (0,tProd x P Q) => if maybeD tct (P) then
                              rQ <- findPropRepresentation proof tct fuel (tLambda x P Q) 1 envTerm env;;
                              ret (mergeOne proof tct envTerm qMergeFormForall qMergeForall (tLambda x P Q) rQ)
                         else
                              rP <- findPropRepresentation proof tct fuel P 0 envTerm env;;
                              Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                              rQ <- findPropRepresentation proof tct fuel Ql 0 envTerm env;;
                              ret (mergeTwo proof tct envTerm qMergeFormImpl qMergeImpl P Ql rP rQ)
    | (S n,tLambda x T P) => if maybeD tct T then
          let envTermSub := raiseEnvTerm tct (tRel 0) (addRelIndex 0 1 envTerm) in
          let envSub := appendAndLift env (ret 0) in
          k <- findPropRepresentation proof tct fuel P n envTermSub envSub;; (match proof return ipT proof->proofRT proof with true => fun '(tk,pk) =>
          ret (tk,(tLambda x (tApp qD ([tct])) pk)) | false => ret end) k
         else ffail
    | _ => ffail end end.
    (* like the above but again the no-proof version *)
    Fixpoint findPropRepresentationNP (tct:Ast.term) (fuel:nat) (t:Ast.term) (frees:nat) (envTerm:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (Ast.term)) := 
    match fuel with 0 => fail "Out of fuel" | S fuel => 
      let ffail := orelse (match @formReifierReifyHelper _ te with None => fail "none" | Some k => rr <- k false tct fuel t frees envTerm env (fun pr t f et e => v <- findPropRepresentationNP tct fuel t f et e;; match pr return proofRT pr with false=>ret (v)|true => ret(v,noProofDummy) end) (fun pr l t et e => v <- findTermRepresentationNP l fuel t et e;;match pr return proofRT pr with false=>ret (v)|true => ret(v,noProofDummy) end);;ret rr end)  
                          (fail ("Cannot represent form " ++ string_of_term t)) in match (frees,t) with
      (0,(baseLogicConn name nil)) => reifyBaseNP name tct nil fuel envTerm env (findPropRepresentationNP tct fuel) (fun tct => findTermRepresentationNP tct fuel)
    | (0,(tApp (baseLogicConn name nil) lst)) => reifyBaseNP name tct lst fuel envTerm env (findPropRepresentationNP tct fuel) (fun tct => findTermRepresentationNP tct fuel)
    | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
            Some ([fnc;v]) => vr <- recoverVector v;;reifyFormNP fnc tct vr envTerm (fun t => findTermRepresentationNP tct fuel t envTerm env)
          | _ => ffail end else if Checker.eq_term init_graph arg qIff then reifyIffNP tct lst fuel envTerm env (findPropRepresentationNP tct fuel) (fun tct => findTermRepresentationNP tct fuel) else ffail
    | (0,tProd x P Q) => if maybeD tct (P) then
                              tQ <- findPropRepresentationNP tct fuel (tLambda x P Q) 1 envTerm env;; 
                              ret (tApp qMergeFormForall ([tct;tQ]))
                         else
                              tP <- findPropRepresentationNP tct fuel P 0 envTerm env;;
                              Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                              tQ <- findPropRepresentationNP tct fuel Ql 0 envTerm env;; 
                              ret (tApp qMergeFormImpl ([tct;tP;tQ]))
    | (S n,tLambda x T P) => if maybeD tct T then
          let envTermSub := raiseEnvTerm tct (tRel 0) (addRelIndex 0 1 envTerm) in
          let envSub := appendAndLift env (ret 0) in
          tk <- findPropRepresentationNP tct fuel P n envTermSub envSub;;
          ret (tk)
         else ffail
    | _ => ffail end end.
End MainReificationFunctions.

(* Given an env and an env helper, represent a statement about D (find a from and a proof that represents it *)
Definition FUEL := 100. 
Ltac representEnvP env env2:= 
match goal with [ |- @representableP ?i ?n ?G ] =>
  let rep := fresh "rep" in let prf := fresh "prf" in let k y := (destruct y as [rep prf]) in
  (*pose ((match env1 with None => @emptyEnv i | Some kk => kk end)) as env;*)
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmInferInstance None (tarski_reflector_extensions i)) (fun treO => let tre := match treO with my_Some kk => kk | my_None => defaultExtensions i end in
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t (@findPropRepresentation i tre true tct FUEL g n qe env2)) (fun '(tPq,pPq) => 
                         monad_utils.bind (tmUnquoteTyped (form) tPq) (fun tP:form => 
                         monad_utils.bind (tmUnquoteTyped (@representsP i n tP env G) pPq) (fun tQ : @representsP i n tP env G =>
                         monad_utils.ret (@existT form (fun mm => @representsP i n mm env G) tP tQ))))))))) k)
  ;exists rep;exists env;exact prf 
end.

(* Like the above, but no-proof mode. We hope easy can proof it*)
Ltac representEnvPNP env env2:= 
match goal with [ |- @representableP ?i ?n ?G ] =>
  let rep := fresh "rep" in let prf := fresh "prf" in let k y := (pose y as rep) in
  (*pose ((match env1 with None => @emptyEnv i | Some kk => kk end)) as env;*)
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmInferInstance None (tarski_reflector_extensions i)) (fun treO => let tre := match treO with my_Some kk => kk | my_None => defaultExtensions i end in
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t (kkk <- (@findPropRepresentation i tre false tct FUEL g n qe env2);;ret kkk)) (fun tPq => 
                         monad_utils.bind (tmUnquoteTyped (form) tPq) (fun tP:form => 
                         monad_utils.ret (tP)))))))) k)
  ;exists rep;exists env;try easy 
end.

(* Like the above, but no-proof mode. We hope easy can proof it*)
Ltac representEnvPNPFast env env2:= 
match goal with [ |- @representableP ?i ?n ?G ] =>
  let rep := fresh "rep" in let prf := fresh "prf" in let k y := (pose y as rep) in
  (*pose ((match env1 with None => @emptyEnv i | Some kk => kk end)) as env;*)
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmInferInstance None (tarski_reflector_extensions i)) (fun treO => let tre := match treO with my_Some kk => kk | my_None => defaultExtensions i end in
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t ((@findPropRepresentationNP i tre tct FUEL g n qe env2))) (fun tPq => 
                         monad_utils.bind (tmUnquoteTyped (form) tPq) (fun tP:form => 
                         monad_utils.ret (tP)))))))) k)
  ;exists rep;exists env;try easy 
end.

(* Construct the environment, then invoke another ltac *)
Definition HiddenTerm {X:Type} {x:X} := x.
Ltac constructEnvCont cont := 
match goal with [ |- @representableP ?i ?n ?G ] => (*(pose (fst y) as envBase;pose (snd y) as envTerm*)
  (*let envBase := fresh "envBase" in let envTerm := fresh "envTerm" in *)
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmInferInstance None (tarski_reflector_extensions i)) (fun treO => let tre := match treO with my_Some kk => kk | my_None => defaultExtensions i end in
                         monad_utils.bind (tmQuote (@emptyEnv i)) (fun baseEnv => 
                         monad_utils.bind (f2t ((@findUnboundVariablesForm i tre tct FUEL g n))) (fun lst => 
                         let '(envToDR,envToNat) := (createEnvTerms tct lst baseEnv) in
                         monad_utils.bind (tmUnquoteTyped (nat -> @D i) envToDR) (fun envToD => 
                         monad_utils.ret (pair envToD envToNat)))))))) cont)
end.
(* Construct the env, then bind it to envBase and envTerm *)
Ltac constructEnv' envBase envTerm := match goal with [ |- @representableP ?i ?n ?G ] => let k y := (pose (@HiddenTerm (nat -> @D i) (fst y)) as envBase;pose (@HiddenTerm (Ast.term -> FailureMonad nat) (snd y)) as envTerm) in constructEnvCont k end. 
Ltac constructEnv := let envBase := fresh "envBase" in let envTerm := fresh "envTerm" in constructEnv' envBase envTerm.

(* First build the env, then use it to proof representability*)
Ltac represent := match goal with [ |- @representableP ?i ?n ?G ] => let tac k := (let envBase := fresh "envBase" in (pose (@HiddenTerm (nat -> @D i) (fst k)) as envBase); representEnvP envBase (snd k)) in constructEnvCont tac end.
Ltac representNP := match goal with [ |- @representableP ?i ?n ?G ] => let tac k := (let envBase := fresh "envBase" in (pose (@HiddenTerm (nat -> @D i) (fst k)) as envBase); representEnvPNP envBase (snd k)) in constructEnvCont tac end.
Ltac representNPFast := match goal with [ |- @representableP ?i ?n ?G ] => let tac k := (let envBase := fresh "envBase" in (pose (@HiddenTerm (nat -> @D i) (fst k)) as envBase); representEnvPNPFast envBase (snd k)) in constructEnvCont tac end.
Ltac representNPVeryFast := match goal with [ |- @representableP ?i ?n ?G ] => representEnvPNPFast ((@emptyEnv i)) (fun t:Ast.term => @fail nat "Unbound") end.
(*Ltac representNP := let envBase := fresh "envBase" in let envTerm := fresh "envTerm" in constructEnv' envBase envTerm; representEnvPNP envBase envTerm.*)

