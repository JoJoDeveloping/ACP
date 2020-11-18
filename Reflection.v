Require Import MetaCoq.Checker.Checker.
From MetaCoq.Template Require Import utils All Pretty.
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
(*Compute (phi[zero..]).
  Compute (phi[zero .: S >> var]).*)

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

  Notation iO := (i_f (f:=Zero) (Vector.nil D)).
  Notation "'iσ' d" := (i_f (f:=Succ) (Vector.cons d (Vector.nil D))) (at level 37).
  Notation "x 'i⊕' y" := (i_f (f:=Plus) (Vector.cons x (Vector.cons y (Vector.nil D)))) (at level 39).
  Notation "x 'i⊗' y" := (i_f (f:=Mult) (Vector.cons x (Vector.cons y (Vector.nil D)))) (at level 38).
  Notation "x 'i=' y" := (i_P (P:=Eq)   (Vector.cons x (Vector.cons y (Vector.nil D)))) (at level 40).
  Hypothesis equality : forall a b, a i= b <-> a = b.
  Definition iμ k := iter (fun x => iσ x) k iO.
  Fixpoint naryProp (n:nat) : Type := match n with 0 => Prop | S nn => D -> naryProp nn end.
  Fixpoint representsP {n:nat} phi rho : (forall (P:naryProp n), Prop) := match n return (forall (P:naryProp n), Prop) with
       0  => (fun (P:Prop) => P <-> rho ⊨ phi)
    | S n => (fun (P:D -> naryProp n) => forall d, @representsP n phi (d.:rho) (P d)) end.
  Definition representableP (n:nat) (P : naryProp n) := exists phi rho, representsP phi rho P.
  Definition representsF (d:D) trm rho := eval rho trm = d.
  Definition representableF (d:D) := exists trm rho, representsF d trm rho.

Definition mergeAnd (rho:nat -> D) (P Q : naryProp 0) : {phi:form & representsP phi rho P} -> {phi:form & representsP phi rho Q} -> {phi:form & @representsP 0 phi rho (P /\ Q)}.
Proof.
intros [phiP HP] [phiQ HQ].
pose (phiP∧phiQ). exists f. destruct HP as [pPl pPr]. destruct HQ as [pQl pQr]. unfold f. split.
* intros [pP pQ]. split. now apply pPl. now apply pQl.
* intros [pP pQ]. split. now apply pPr. now apply pQr.
Defined.

Definition mergeFalse (rho:nat -> D) : {phi:form & @representsP 0 phi rho False}.
Proof. exists fal. easy. Defined.

Definition mergeOr (rho:nat -> D) (P Q : naryProp 0) : {phi:form & representsP phi rho P} -> {phi:form & representsP phi rho Q} -> {phi:form & @representsP 0 phi rho (P \/ Q)}.
Proof.
intros [phiP HP] [phiQ HQ].
pose (phiP∨phiQ). exists f. destruct HP as [pPl pPr]. destruct HQ as [pQl pQr]. unfold f. split.
* intros [pP|pQ]. left; now apply pPl. right; now apply pQl.
* intros [pP|pQ]. left; now apply pPr. right; now apply pQr.
Defined.

Definition mergeImpl (rho:nat -> D) (P Q : naryProp 0) : {phi:form & representsP phi rho P} -> {phi:form & representsP phi rho Q} -> {phi:form & @representsP 0 phi rho (P -> Q)}.
Proof.
intros [phiP HP] [phiQ HQ].
pose (phiP-->phiQ). exists f. destruct HP as [pPl pPr]. destruct HQ as [pQl pQr]. unfold f. split.
* intros PQ pP. apply pQl, PQ, pPr, pP.
* cbn. intros pPQ pP. apply pQr, pPQ, pPl, pP.
Defined.

Definition mergeExists (rho:nat -> D) (P:naryProp 1) : {phi:form & representsP phi rho P} -> {phi:form & @representsP 0 phi rho (exists q:D, P q)}.
Proof.
intros [phi pR].
pose (∃ phi). exists f. split.
* intros [q Pq]. exists q. destruct (pR q) as [pRl pRr]. now apply pRl.
* intros [q Pq]. exists q. destruct (pR q) as [pRl pRr]. now apply pRr.
Defined.
(*
Definition mergeForall (rho:nat -> D) (P:naryProp 1) : {phi:form & representsP phi rho P} -> {phi:form & @representsP 0 phi rho (forall q:D, P q)}.
Proof.
intros [phi pR].
pose (∀ phi). exists f. split.
* intros H q. destruct (pR q) as [pRl pRr]. now apply pRl, H.
* intros H q. destruct (pR q) as [pRl pRr]. now apply pRr, H.
Defined.*)

Definition mergeZero (rho:nat -> D) :{phi:term & representsF (iO) phi rho}.
Proof.
exists zero. easy.
Defined.

Definition mergeSucc (rho:nat -> D) (d:D) : {phi:term & representsF d phi rho} -> {phi:term & representsF (iσ d) phi rho}.
Proof. intros [t pt].
pose (σ t). exists t0. unfold t0. unfold representsF. cbn. now rewrite pt.
Defined.

Definition mergeAdd (rho:nat -> D) (d1 d2:D) : {phi:term & representsF d1 phi rho} -> {phi:term & representsF d2 phi rho} -> {phi:term & representsF (d1 i⊕ d2) phi rho}.
Proof. intros [t1 pt1] [t2 pt2].
pose (t1 ⊕ t2). exists t. unfold t. unfold representsF. cbn. now rewrite pt1, pt2.
Defined.

Definition mergeMul (rho:nat -> D) (d1 d2:D) : {phi:term & representsF d1 phi rho} -> {phi:term & representsF d2 phi rho} -> {phi:term & representsF (d1 i⊗ d2) phi rho}.
Proof. intros [t1 pt1] [t2 pt2].
pose (t1 ⊗ t2). exists t. unfold t. unfold representsF. cbn. now rewrite pt1, pt2.
Defined.

Definition mergeEq (rho:nat -> D) (d1 d2 : D) : {phi:term & representsF d1 phi rho} -> {phi:term & representsF d2 phi rho} -> {phi:form & @representsP 0 phi rho (d1 i= d2)}.
Proof. intros [t1 pt1] [t2 pt2].
pose (t1 == t2). exists f. cbn. now rewrite pt1, pt2.
Defined.

Definition mergeEqProp (rho:nat -> D) (d1 d2 : D) : {phi:term & representsF d1 phi rho} -> {phi:term & representsF d2 phi rho} -> {phi:form & @representsP 0 phi rho (d1 = d2)}.
Proof. intros [t1 pt1] [t2 pt2].
pose (t1 == t2). exists f. cbn. now rewrite pt1, pt2.
Defined.

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
Notation termConstructorBase := (tConst (MPfile (["Tarski"; "Arith"]), "i_f") nil).
Notation propConstructorBase := (tConst (MPfile (["Tarski"; "Arith"]), "i_P") nil).
Definition termPropRepStart := 
   ([tConst (MPfile (["Reflection"; "Arith"]), "PA_funcs_signature") nil;
   tConst (MPfile (["Reflection"; "Arith"]), "PA_preds_signature") nil; tVar "D"; 
   tVar "I"]).

Fixpoint recoverVector (f : Ast.term) {struct f}: TemplateMonad (list Ast.term) := let fail := tmPrint f;;tmFail "not a vector application" in match f with
  vectorNil _ => ret nil
| vectorCons x _ _ xr => xrl <- recoverVector xr;;ret (x::xrl)
| _ => fail
end.

Existing Instance config.default_checker_flags.
Fixpoint popListStart (l : list Ast.term) (ls : list Ast.term) : option (list Ast.term) := match (l,ls) with
  (a,nil)=> Some a
| (lx::lxr, lsx::lsxr) => if Checker.eq_term init_graph lx lsx then popListStart lxr lsxr else None
| _ => None end.

Definition FUEL := 100. 

Definition termReifier := list Ast.term -> Ast.term -> (Ast.term -> TemplateMonad (prod term Ast.term)) -> TemplateMonad (prod term Ast.term).
Definition reifyZero : termReifier := fun l env fTR => match l with nil => v <- tmQuote mergeZero;;ret (pair (zero) (tApp (v) ([env]))) | _ => tmFail "Zero constructor applied to != 0 terms" end.
Definition reifySucc : termReifier := fun l env fTR => match l with [x] => 
                                           v <- tmQuote (mergeSucc);;
                                           '(tx,xr) <- fTR x ;; ret (σ tx,tApp v ([env;x;xr])) | _ => tmFail "Succ constructor applied to != 1 terms" end.
Definition reifyAdd : termReifier := fun l env fTR => match l with [x; y] =>  
                                           v <- tmQuote (mergeAdd) ;;
                                           '(tx,xr) <- fTR x ;; '(ty,yr) <- fTR y ;; ret (tx⊕ty,tApp v ([env;x;y;xr;yr])) | _ => tmFail "Add constructor applied to != 2 terms" end.
Definition reifyMul : termReifier := fun l env fTR => match l with [x; y] =>  
                                           v <- tmQuote (mergeMul) ;;
                                           '(tx,xr) <- fTR x ;; '(ty,yr) <- fTR y ;; ret (tx⊗ty,tApp v ([env;x;y;xr;yr])) | _ => tmFail "Mul constructor applied to != 2 terms" end.
Definition reifyTerm (n:nat) : termReifier := match n with
0 => reifyZero | 1 => reifySucc | 2 => reifyAdd | 3 => reifyMul | _ => fun _ _ _ => tmFail ("Unknown term constructor index " ++ string_of_nat n) end.
Definition reifyRelHelper (rho:nat -> D) (d:D) (n:nat) (H:rho n = d) : {phi:term & representsF d phi rho}.
Proof.
exists ($n). exact H.
Defined.



Notation termRepDet i v := (([tConstruct {| inductive_mind := (MPfile (["Reflection"; "Arith"]), "PA_funcs"); inductive_ind := 0 |}
     i nil; v])).
Notation formRepDet i v := (([tConstruct {| inductive_mind := (MPfile (["Reflection"; "Arith"]), "PA_preds"); inductive_ind := 0 |}
     i nil; v])).
MetaCoq Quote Definition zeroEnv := (fun k:nat => iO).
MetaCoq Quote Definition qeq_refl := (@eq_refl).

Fixpoint findTermRepresentation (fuel:nat) (t:Ast.term) (termEnv:Ast.term) (env:Ast.term -> TemplateMonad nat) {struct fuel}: (TemplateMonad (prod term Ast.term)) := 
  let fail := (v <- tmQuote reifyRelHelper;;envv <- env (t);;num <- tmQuote (envv);;ret ($envv,tApp v ([termEnv;t;num;tApp qeq_refl ([tVar "D";t])]))) in match fuel with 
    0 => tmFail "Out of fuel" 
    | S fuel => match t with
        tApp termConstructorBase l => match popListStart l termPropRepStart with
          Some (termRepDet i v) => vr <- recoverVector v;;reifyTerm i vr termEnv (fun t => findTermRepresentation fuel t termEnv env)
         | _ => fail end
      | _ => fail
    end 
  end.


Definition proj1 {A:Type} {B:A -> Type} : {a:A & B a} -> A := fun z => match z with existT x _ => x end.
Definition mergeForall2 (rho:nat -> D) (Q:naryProp 0) (H:{PP : naryProp 1 & (forall x:D, PP x) <-> Q}) : {phi:form & representsP phi rho (proj1 H)} -> {phi:form & @representsP 0 phi rho Q}.
Proof.
intros [phi pR]. destruct H as [PP [eql eqr]]. cbn in pR.
pose (∀ phi). exists f. split.
* intros H q. destruct (pR q) as [pRl pRr]. now apply pRl, eqr, H.
* intros H. apply eql. intros q. destruct (pR q) as [pRl pRr]. now apply pRr, H.
Defined.


(*
Definition representForallP (Q:Prop) := a <- tmQuote (Q);; aa <- abstractForall a;;p <- tmUnquoteTyped ({P:naryProp 1 & (forall d:D, P d) <-> Q}) aa;; ret p.

MetaCoq Run (let Q:=forall x:D, x i= iO in 
    representForallP Q).

Ltac representForall k:= match goal with [ k : ?Q |- _ ] =>
  let fr := fresh "rep" in let kkk := fresh "sml" in let pr := fresh "denv" in let k y := (pose y as fr) in
  (run_template_program (representForallP Q) k)
  end.

Lemma stuff : true.
pose (forall x:nat, x > 0).
(run_template_program (representForallP (forall x : D, x i= iO)) (let k y := (pose y) in k)).


Definition lol := iO.
MetaCoq Quote Definition lolEnv := (fun n:nat => lol).
Definition phiRepr (rho:nat -> D) (t:D) := {phi:term & representsF t phi rho}.
MetaCoq Run (let trm := lol i⊕ (iσ iO) in a <- tmQuote (trm);;
v <- findTermRepresentation FUEL a lolEnv (fun _:Ast.term => ret 0);;k<-tmUnquoteTyped (phiRepr (fun n:nat => lol) trm) v;;tmDefinition "aa" k).
*)

Definition envTermReifier := list Ast.term -> nat -> Ast.term -> (Ast.term -> TemplateMonad nat) -> (Ast.term -> TemplateMonad (prod form Ast.term)) -> TemplateMonad (prod form Ast.term).
Definition refiyEq : envTermReifier := fun l fuel envTerm env fPR => match l with [x; y] =>  
                                           v <- tmQuote mergeEq;;
                                           '(tx,xr) <- findTermRepresentation fuel x envTerm env ;;
                                           '(ty,yr) <- findTermRepresentation fuel y envTerm env ;; 
                                           ret (tx==ty,tApp v ([envTerm;x;y;xr;yr])) | _ => tmFail "Eq constructor applied to != 2 terms" end.
Definition reifyForm (n:nat) : envTermReifier := match n with 0 => refiyEq | _ => fun _ _ _ _ _ => tmFail ("Unknown form constructor index " ++ string_of_nat n) end.

Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
Definition baseConnectiveReifier := list Ast.term -> nat -> Ast.term -> (Ast.term -> TemplateMonad nat) -> (Ast.term -> nat -> Ast.term -> (Ast.term -> TemplateMonad nat) -> TemplateMonad (prod form Ast.term))-> TemplateMonad (prod form Ast.term).
Definition reifyAnd : baseConnectiveReifier := fun lst _ envTerm env fPR => match lst with [x; y] => v <- tmQuote mergeAnd;;
                                           '(tx,xr) <- fPR x 0 envTerm env;;'(ty,yr) <- fPR y 0 envTerm env;; ret (tx∧ty,tApp v ([envTerm;x;y;xr;yr])) | _ => tmFail "And applied to != 2 terms" end.
Definition reifyOr  : baseConnectiveReifier := fun lst _ envTerm env fPR => match lst with [x; y] => v <- tmQuote mergeOr;;
                                           '(tx,xr) <- fPR x 0 envTerm env;;'(ty,yr) <- fPR y 0 envTerm env;; ret (tx∨ty,tApp v ([envTerm;x;y;xr;yr])) | _ => tmFail "Or applied to != 2 terms" end.
Definition reifyExist:baseConnectiveReifier := fun lst _ envTerm env fPR => match lst with [_; P] => v <- tmQuote mergeExists;;
                                           '(tP,rr) <- fPR P 1 envTerm env;; ret (∃ tP,tApp v ([envTerm;P;rr])) | _ => tmFail "Exist applied to wrong terms" end.
Definition refiyCoqEq : baseConnectiveReifier := fun l fuel envTerm env fPR => match l with [tVar "D"; x; y] =>  
                                           v <- tmQuote mergeEqProp;;
                                           '(tx,xr) <- findTermRepresentation fuel x envTerm env ;;
                                           '(ty,yr) <- findTermRepresentation fuel y envTerm env ;; 
                                           ret (tx==ty,tApp v ([envTerm;x;y;xr;yr])) | _ => tmFail "Eq constructor applied to != 2 terms" end.
Definition reifyBase (s:string) : baseConnectiveReifier := match s with "and" => reifyAnd | "or" => reifyOr | "ex" => reifyExist | "eq" => refiyCoqEq | _ => fun _ _ _ _ _ => tmFail ("Unknown connective "++s) end.


Fixpoint raiseRelIndex (minn:nat) (t:Ast.term) : Ast.term := match t with
  tRel n => if Compare_dec.le_gt_dec minn n then tRel (S n) else tRel n
| tVar k => tVar k
| tEvar n ls => tEvar n (map (raiseRelIndex minn) ls)
| tSort u => tSort u
| tCast t ck t2 => tCast (raiseRelIndex minn t) ck (raiseRelIndex minn t2)
| tProd n t v => tProd n (raiseRelIndex minn t) (raiseRelIndex (S minn) v)
| tLambda n t v => tLambda n (raiseRelIndex minn t) (raiseRelIndex (S minn) v)
| tLetIn n t v e => tLetIn n (raiseRelIndex minn t) (raiseRelIndex minn v) (raiseRelIndex (S minn) e)
| tApp f al => tApp f (map (raiseRelIndex minn) al)
| tConst a b => tConst a b
| tInd i t => tInd i t
| tConstruct a b c => tConstruct a b c
| tCase k i r m => tCase k (raiseRelIndex minn i) (raiseRelIndex minn r) (map (fun '(a,b) => (a,raiseRelIndex minn b)) m)
| tProj p t => tProj p (raiseRelIndex minn t)
| tFix mft n => tFix (map (map_def (raiseRelIndex minn) (raiseRelIndex (S minn))) mft) n
| tCoFix mft n => tCoFix (map (map_def (raiseRelIndex minn) (raiseRelIndex (S minn))) mft) n
end.


Notation qProp := (tSort (Universe.from_kernel_repr (Level.lProp, false) nil)).

MetaCoq Quote Definition qnaryProp1 := Eval compute in (naryProp 1).
MetaCoq Quote Definition qexistT := @existT.
MetaCoq Quote Definition qiff := @iff.
MetaCoq Quote Definition qcong := @conj.
(*MetaCoq Test Quote (@existT (naryProp 1) (fun P => (forall d:D, P d) <-> (forall d:D,False)) (fun _ => False) (conj (fun (k:(forall d:D,False))=>k) (fun (k:(forall d:D,False))=>k))).*)

Definition abstractForall (t:Ast.term) : TemplateMonad (Ast.term) :=
match t with tProd x t v =>
    let prop := tLambda x t v in
    let raisedV := raiseRelIndex 0 (tProd x t v) in
    ret (tApp (qexistT) ([qnaryProp1; tLambda (nNamed "P") qnaryProp1 (tApp qiff 
                ([tProd x t (tApp (tRel 1) ([tRel 0])); raisedV]));
                 tLambda x t v; tApp qcong ([
tProd (nNamed "x") (tProd x t v) raisedV;
tProd (nNamed "x") (tProd x t v) raisedV;
tLambda (nNamed "k") (tProd x t v) (tRel 0);
tLambda (nNamed "k") (tProd x t v) (tRel 0)
])]))
| _ => tmPrint t;;tmFail "called abstractForall on something not a product" end.


Definition pred (n:nat) := match n with 0 => 0 | S n => n end.
Fixpoint flatten_monad {A:Type} (l:list (TemplateMonad A)) : TemplateMonad (list A) := match l with nil => ret nil | x::xr => xm <- x;; xrm <- flatten_monad xr;; ret (xm::xrm) end.
Definition map_monad {A B:Type} (f:A -> TemplateMonad B) (l:list A) : TemplateMonad (list B) := flatten_monad (map f l).
Definition map_def_monad {A B : Type} (tyf bodyf : A -> TemplateMonad B) (d:def A) : TemplateMonad (def B) := dtr <- tyf (dbody d);;dbr <- bodyf (dbody d);; ret {|
dname := dname d;
dtype := dtr;
dbody := dbr;
rarg := rarg d |}.
Check (Compare_dec.le_gt_dec).
Fixpoint lowerRelIndex (minn:nat) (tv:TemplateMonad Ast.term) (t:Ast.term) {struct t}: TemplateMonad Ast.term := match t with
  tRel n => if Compare_dec.le_gt_dec minn n then if Compare_dec.le_gt_dec minn (S n) then tmPrint "pred";;tmPrint (tRel (pred n));;ret (tRel (pred n)) else tmPrint (minn,n);;tv else tmPrint "inside";;ret (tRel n)
| tVar k => ret (tVar k)
| tEvar n ls => m <- map_monad (lowerRelIndex minn tv) ls;;ret (tEvar n m)
| tSort u => ret (tSort u)
| tCast t ck t2 => mt <- (lowerRelIndex minn tv t);;mt2<-(lowerRelIndex minn tv t2);;ret (tCast mt ck mt2)
| tProd n t v => mt<-(lowerRelIndex minn tv t);;mv<-(lowerRelIndex (S minn) tv v);;ret (tProd n mt mv)
| tLambda n t v => mt<-(lowerRelIndex minn tv t);;mv<-(lowerRelIndex (S minn) tv v);;ret (tLambda n mt mv)
| tLetIn n t v e => mt<-(lowerRelIndex minn tv t);;mv<-(lowerRelIndex minn tv v);;me<-(lowerRelIndex (S minn) tv e);;ret (tLetIn n mt mv me)
| tApp f al => mal<-(map_monad (lowerRelIndex minn tv) al);;ret (tApp f mal)
| tConst a b => ret (tConst a b)
| tInd i t => ret (tInd i t)
| tConstruct a b c => ret (tConstruct a b c)
| tCase k i r m => mi<-(lowerRelIndex minn tv i);;mr<-(lowerRelIndex minn tv r);;mm<-(map_monad (fun '(a,b) => mb <- lowerRelIndex minn tv b;; ret (a,mb)) m);;ret (tCase k mi mr mm)
| tProj p t => mt<-(lowerRelIndex minn tv t);;ret (tProj p mt)
| tFix mft n => mmft<-(map_monad (map_def_monad (lowerRelIndex minn tv) (lowerRelIndex (S minn) tv)) mft);;ret (tFix mmft n)
| tCoFix mft n => mmft<-(map_monad (map_def_monad (lowerRelIndex minn tv) (lowerRelIndex (S minn) tv)) mft);;ret (tCoFix mmft n)
end.

Definition appendZero (env:Ast.term -> TemplateMonad nat) (zv:TemplateMonad nat) : (Ast.term -> TemplateMonad nat) := 
      fun (t:Ast.term) => match t with tRel n => (match n with 0 => zv | S n => env (tRel n) end) | _ => tmFail "stuff" end. (*k <- lowerRelIndex 0 (tmFail "Error 1337") t;; (env k) end.*)
Definition appendAndLift (env:Ast.term -> TemplateMonad nat) (zv:TemplateMonad nat) : (Ast.term -> TemplateMonad nat) := 
      fun t => match t with tRel n => (match n with 0 => zv | S n => k <- env (tRel n);;ret (S k) end) | _ => tmFail "stuff2" end. (*k <- lowerRelIndex 0 (tmFail "Error 1337") t;; v <- env k;;ret (S v) end.*)
MetaCoq Quote Definition qraiseEnvTerm := (fun (d:D) (rho:nat -> D) => d .: rho).
Definition raiseEnvTerm (d:Ast.term) (env:Ast.term) : Ast.term := tApp (qraiseEnvTerm) ([d;raiseRelIndex 0 env]).

Definition mergeFreeVarIntro (rho:nat -> D) (n:nat) (P:naryProp (S n)) (H:forall d:D, {phi:form & representsP phi (d.:rho) (P d)}) (H2:forall d:D, proj1 (H iO) = proj1 (H d)) : {phi:form & representsP phi rho P}.
Proof.
pose (proj1 (H (iO))). exists f. intros k. destruct (H k) as [trm prf] eqn:Heq. specialize (H2 k). rewrite Heq in H2. cbn in H2. unfold f. rewrite H2. exact prf.
Defined.
MetaCoq Quote Definition qform := form.
(*

Definition mergeForall2 (rho:nat -> D) (Q:naryProp 0) (H:{PP : naryProp 1 & (forall x:D, PP x) <-> Q}) : {phi:form & representsP phi rho (proj1 H)} -> {phi:form & @representsP 0 phi rho Q}.
Proof.
intros [phi pR]. destruct H as [PP [eql eqr]]. cbn in pR.
pose (∀ phi). exists f. split.
* intros H q. destruct (pR q) as [pRl pRr]. now apply pRl, eqr, H.
* intros H. apply eql. intros q. destruct (pR q) as [pRl pRr]. now apply pRr, H.
Defined.
*)

Fixpoint findPropRepresentation (fuel:nat) (t:Ast.term) (frees:nat) (envTerm:Ast.term) (env:Ast.term -> TemplateMonad nat) {struct fuel}: (TemplateMonad (prod form Ast.term)) := tmPrint t;;
let fail :=tmPrint (frees,t);;tmFail ("Cannot represent form") in match fuel with 0 => tmFail "Out of fuel" | S fuel => 
  match (frees,t) with
  (0,(baseLogicConn "False" nil)) => v <- tmQuote mergeFalse;;ret (fal,tApp v ([envTerm]))
| (0,(tApp (baseLogicConn name nil) lst)) => reifyBase name lst fuel envTerm env (findPropRepresentation fuel)
| (0,(tApp propConstructorBase lst)) => match popListStart lst termPropRepStart with
        Some (formRepDet i v) => vr <- recoverVector v;;reifyForm i vr fuel envTerm env (fun t => findPropRepresentation fuel t frees envTerm env)
      | _ => fail end
| (0,tProd x (tVar "D") Q) =>
      k <- abstractForall (tProd x (tVar "D") Q);;
      '(frm,tQ) <- findPropRepresentation fuel (tLambda x (tVar "D") Q) 1 envTerm env;;
      v <- tmQuote mergeForall2;;
      ret (∀ frm, tApp v ([envTerm;tProd x (tVar "D") Q;k;tQ]))
| (0,tProd _ P Q) =>
      v <- tmQuote mergeImpl;;
      '(tP,rP) <- findPropRepresentation fuel P 0 envTerm env;;
      Ql <- lowerRelIndex 0 (tmFail "Used var of implication precondition") Q;;
      '(tQ,rQ) <- findPropRepresentation fuel Ql 0 envTerm env;;
      ret (tP --> tQ,tApp v ([envTerm;P;Ql;rP;rQ]))
| (S n,tLambda x (tVar "D") P) => 
      let envTermSub := raiseEnvTerm (tRel 0) envTerm in
      let envSub := appendAndLift env (ret 0) in
      '(frm,k) <- findPropRepresentation fuel P n envTermSub envSub;;
      v <- tmQuote mergeFreeVarIntro;;
      num <- tmQuote n;;
      vfrmq <- tmQuote frm;;
      ret (frm,tApp v ([envTerm;num;tLambda x (tVar "D") P;tLambda x (tVar "D") k;tLambda x (tVar "D") (tApp qeq_refl ([qform;vfrmq]))]))
| _ => fail end end.

Check print_term.
MetaCoq Quote Recursively Definition k := mergeFreeVarIntro.
Check (fst k).
Definition genv := empty_ext (fst k).

Ltac representEnv env := match goal with [ |- representableP ?n ?G ] =>
  let rep := fresh "rep" in let prf := fresh "prf" in let hyp := fresh "H" in let k y := (idtac y;destruct y as [rep prf]) in
  (run_template_program (g <- (tmQuote G);;qe <- tmQuote env;;'(aaa,rp)<-findPropRepresentation FUEL g n qe (fun v => tmFail "unbound");;tmPrint (aaa,rp);;(*print_term genv nil false rp*)tmUnquoteTyped ({phi:form & @representsP n phi env G}) rp) k)
  ;exists rep;exists env;exact prf
end.
Ltac represent := representEnv (fun k:nat => iO).

Goal (representableP 0 (iO i= iO)).
represent.
Qed.

Goal (representableP 0 (forall d:D, d i= iO)).
represent.
Qed.

Goal (representableP 1 (fun a => False -> a i= a)).
represent.
Qed.

Goal (representableP 2 (fun (d e :D) => forall g, exists j, g i= d i⊕ j /\ False -> False \/ (e i⊗ e i= iσ j /\ False))).
represent.


Goal (forall n:nat, representableF (iμ n)).
intros n. induction n as [|n [phi [rho IH]]].
* cbn. exists zero. pose (fun (n:nat) => iO). exists d. split.
* cbn. unfold representableF. pose (σ phi). exists t. exists rho. unfold representsF. unfold representsF in IH. unfold t. cbn. now rewrite IH.
Qed.

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
    representableP 1 P -> P iO -> (forall d, P d -> P (iσ d)) -> forall d, P d.
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
    specialize (H (fun _ => iO)). cbn in H. specialize (H d). revert H.
    rewrite equality. cbn.
    intros [<- | [x H]]. now left. right. rewrite equality in H. now exists x.
    apply zero_or_succ.
  Qed.

  Goal forall d, iO i= d \/ exists x, d i= iσ x. 
  Proof.
    apply PAinduction. represent.
    - left. now rewrite equality.
    - intros d [HL |]. rewrite equality in HL. cbn in HL. rewrite <- HL. right. pose iO as miO. exists miO. rewrite equality. easy. right. exists d. rewrite equality. easy.
  Qed.

  Lemma add_rec_right :
    forall d n, n i⊕ (iσ d) i= iσ (n i⊕ d).
  Proof.
    apply PAinduction.
    - represent. pose (phi := ∀ $1 ⊕ σ $2 == σ ($1 ⊕ $2) ).
      exists phi. exists (fun _ => n). intros d. cbn. split.
      + intros H d0. rewrite equality. cbn. easy.
      + intros H. specialize (H n). rewrite equality in H. cbn in H. auto.
    - rewrite !add_zero; try reflexivity. all: firstorder.
    - intros d IH. rewrite !add_rec. now rewrite IH. all: firstorder.
  Qed.

End Models.