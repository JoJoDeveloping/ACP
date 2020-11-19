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

Locate ret.

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

Inductive FailureMonad (A:Type) : Type := ret : A -> FailureMonad A | fail : string -> FailureMonad A.
Arguments ret {_} _.
Arguments fail {_} _.
Definition bind {A B : Type} (k:FailureMonad A) (f:A -> FailureMonad B) := match k return FailureMonad B with fail x => fail x | ret k => f k end.
Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)).

Definition mergeAnd (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form) : representsP fP rho P -> representsP fQ rho Q -> @representsP 0 (fP∧fQ) rho (P /\ Q).
Proof.
intros HP HQ.
destruct HP as [pPl pPr]. destruct HQ as [pQl pQr]. split.
* intros [pP pQ]. split. now apply pPl. now apply pQl.
* intros [pP pQ]. split. now apply pPr. now apply pQr.
Defined.

Definition mergeFalse (rho:nat -> D) : @representsP 0 fal rho False.
Proof. easy. Defined.

Definition mergeOr (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form) : representsP fP rho P -> representsP fQ rho Q -> @representsP 0 (fP∨fQ) rho (P \/ Q).
Proof.
intros HP HQ.
destruct HP as [pPl pPr]. destruct HQ as [pQl pQr]. split.
* intros [pP|pQ]. left; now apply pPl. right; now apply pQl.
* intros [pP|pQ]. left; now apply pPr. right; now apply pQr.
Defined.

Definition mergeImpl (rho:nat -> D) (P Q : naryProp 0) (fP fQ : form) : representsP fP rho P -> representsP fQ rho Q -> @representsP 0 (fP --> fQ) rho (P -> Q).
Proof.
intros HP HQ.
destruct HP as [pPl pPr]. destruct HQ as [pQl pQr]. split.
* intros PQ pP. apply pQl, PQ, pPr, pP.
* cbn. intros pPQ pP. apply pQr, pPQ, pPl, pP.
Defined.

Definition mergeExists (rho:nat -> D) (P:naryProp 1) (fP:form) : representsP fP rho P -> @representsP 0 (∃ fP) rho (exists q:D, P q).
Proof.
intros pR. split.
* intros [q Pq]. exists q. destruct (pR q) as [pRl pRr]. now apply pRl.
* intros [q Pq]. exists q. destruct (pR q) as [pRl pRr]. now apply pRr.
Defined.

Definition mergeZero (rho:nat -> D) : representsF (iO) zero rho.
Proof.
easy.
Defined.

Definition mergeSucc (rho:nat -> D) (d:D) (phi:term) : representsF d phi rho -> representsF (iσ d) (σ phi) rho.
Proof. intros pt.
unfold representsF. cbn. now rewrite pt.
Defined.

Definition mergeAdd (rho:nat -> D) (d1 d2:D) (t1 t2 : term) : representsF d1 t1 rho -> representsF d2 t2 rho -> representsF (d1 i⊕ d2) (t1⊕t2) rho.
Proof. intros pt1 pt2.
unfold representsF. cbn. now rewrite pt1, pt2.
Defined.

Definition mergeMul (rho:nat -> D) (d1 d2:D) (t1 t2 : term) : representsF d1 t1 rho -> representsF d2 t2 rho -> representsF (d1 i⊗ d2) (t1⊗t2) rho.
Proof. intros pt1 pt2.
unfold representsF. cbn. now rewrite pt1, pt2.
Defined.

Definition mergeEq (rho:nat -> D) (d1 d2 : D) (t1 t2 : term) : representsF d1 t1 rho -> representsF d2 t2 rho -> @representsP 0 (t1==t2) rho (d1 i= d2).
Proof. intros pt1 pt2.
cbn. now rewrite pt1, pt2.
Defined.

Definition mergeEqProp (rho:nat -> D) (d1 d2 : D) (t1 t2 : term) : representsF d1 t1 rho -> representsF d2 t2 rho -> @representsP 0 (t1==t2) rho (d1 = d2).
Proof. intros pt1 pt2.
cbn. now rewrite pt1, pt2.
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

Fixpoint recoverVector (f : Ast.term) {struct f}: FailureMonad (list Ast.term) := let ffail := fail "not a vector application" in match f with
  vectorNil _ => ret nil
| vectorCons x _ _ xr => xrl <- recoverVector xr;;ret (x::xrl)
| _ => ffail
end.

Existing Instance config.default_checker_flags.
Fixpoint popListStart (l : list Ast.term) (ls : list Ast.term) : option (list Ast.term) := match (l,ls) with
  (a,nil)=> Some a
| (lx::lxr, lsx::lsxr) => if Checker.eq_term init_graph lx lsx then popListStart lxr lsxr else None
| _ => None end.

Definition FUEL := 100. 

Definition termReifier := list Ast.term -> Ast.term -> (Ast.term -> FailureMonad (prod Ast.term Ast.term)) -> FailureMonad (prod Ast.term Ast.term).
MetaCoq Quote Definition qMergeZero := mergeZero.
MetaCoq Quote Definition qMergeZeroTerm := zero.
Definition reifyZero : termReifier := fun l env fTR => match l with nil => ret ((qMergeZeroTerm, tApp (qMergeZero) ([env]))) | _ => fail "Zero constructor applied to != 0 terms" end.
MetaCoq Quote Definition qMergeSucc := mergeSucc.
MetaCoq Quote Definition qMergeSuccTerm := (fun k => σ k).
Definition reifySucc : termReifier := fun l env fTR => match l with [x] => 
                                           k <- fTR x ;; let '(xt,xr) := k in ret (tApp qMergeSuccTerm ([xt]),tApp qMergeSucc ([env;x;xt;xr])) | _ => fail "Succ constructor applied to != 1 terms" end.
MetaCoq Quote Definition qMergeAdd := mergeAdd.
MetaCoq Quote Definition qMergeAddTerm := (fun k l => k⊕l).
Definition reifyAdd : termReifier := fun l env fTR => match l with [x; y] =>  
                                           kx <- fTR x ;; ky <- fTR y ;; let '((xt,xp),(yt,yp)) := (kx,ky) in ret (tApp qMergeAddTerm ([xt;yt]), tApp qMergeAdd ([env;x;y;xt;yt;xp;yp])) | _ => fail "Add constructor applied to != 2 terms" end.
MetaCoq Quote Definition qMergeMul := mergeMul.
MetaCoq Quote Definition qMergeMulTerm := (fun k l => k⊗l).
Definition reifyMul : termReifier := fun l env fTR => match l with [x; y] =>
                                           kx <- fTR x ;; ky <- fTR y ;; let '((xt,xp),(yt,yp)) := (kx,ky) in ret (tApp qMergeMulTerm ([xt;yt]), tApp qMergeMul ([env;x;y;xt;yt;xp;yp])) | _ => fail "Mul constructor applied to != 2 terms" end.
Definition reifyTerm (n:nat) : termReifier := match n with
0 => reifyZero | 1 => reifySucc | 2 => reifyAdd | 3 => reifyMul | _ => fun _ _ _ => fail ("Unknown term constructor index " ++ string_of_nat n) end.
MetaCoq Quote Definition qMergeVarTerm := var.
Definition reifyRelHelper (rho:nat -> D) (d:D) (n:nat) (H:rho n = d) : representsF d ($n) rho.
Proof.
exact H.
Defined.
MetaCoq Quote Definition qRelHelper := reifyRelHelper.
MetaCoq Quote Definition qNatZero := 0.
MetaCoq Quote Definition qNatSucc := S.

Fixpoint quoteNumber (n:nat) : Ast.term:= match n with 0 => qNatZero | S n => tApp qNatSucc ([quoteNumber n]) end.

Notation termRepDet i v := (([tConstruct {| inductive_mind := (MPfile (["Reflection"; "Arith"]), "PA_funcs"); inductive_ind := 0 |}
     i nil; v])).
Notation formRepDet i v := (([tConstruct {| inductive_mind := (MPfile (["Reflection"; "Arith"]), "PA_preds"); inductive_ind := 0 |}
     i nil; v])).
MetaCoq Quote Definition qeq_refl := (@eq_refl).

Fixpoint findTermRepresentation (fuel:nat) (t:Ast.term) (termEnv:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (prod Ast.term Ast.term)) := 
  let ffail := (envv <- env (t);;let num := quoteNumber (envv) in ret (tApp qMergeVarTerm ([num]),tApp qRelHelper ([termEnv;t;num;tApp qeq_refl ([tVar "D";t])]))) in match fuel with 
    0 => fail "Out of fuel" 
    | S fuel => match t with
        tApp termConstructorBase l => match popListStart l termPropRepStart with
          Some (termRepDet i v) => vr <- recoverVector v;;reifyTerm i vr termEnv (fun t => findTermRepresentation fuel t termEnv env)
         | _ => ffail end
      | _ => ffail
    end 
  end.



Definition proj1 {A:Type} {B:A -> Type} : {a:A & B a} -> A := fun z => match z with existT x _ => x end.
Definition mergeForall (rho:nat -> D) (Q:naryProp 0) (H:{PP : naryProp 1 & (forall x:D, PP x) <-> Q}) (phi:form) : representsP phi rho (proj1 H) -> @representsP 0 (∀ phi) rho Q.
Proof.
intros pR. destruct H as [PP [eql eqr]]. cbn in pR. split.
* intros H q. destruct (pR q) as [pRl pRr]. now apply pRl, eqr, H.
* intros H. apply eql. intros q. destruct (pR q) as [pRl pRr]. now apply pRr, H.
Defined.

Definition envTermReifier := list Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> (Ast.term -> FailureMonad (prod Ast.term Ast.term)) -> FailureMonad (prod Ast.term Ast.term).
MetaCoq Quote Definition qMergeEq := mergeEq.
MetaCoq Quote Definition qMergeFormEq := (fun a b => a == b).
Definition refiyEq : envTermReifier := fun l fuel envTerm env fPR => match l with [x; y] =>  
                                           (xr) <- findTermRepresentation fuel x envTerm env ;;
                                           (yr) <- findTermRepresentation fuel y envTerm env ;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                           ret (tApp qMergeFormEq ([xt;yt]), tApp qMergeEq ([envTerm;x;y;xt;yt;xp;yp])) | _ => fail "Eq constructor applied to != 2 terms" end.
Definition reifyForm (n:nat) : envTermReifier := match n with 0 => refiyEq | _ => fun _ _ _ _ _ => fail ("Unknown form constructor index " ++ string_of_nat n) end.

Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
Definition baseConnectiveReifier := list Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> (Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad (prod Ast.term Ast.term))-> FailureMonad (prod Ast.term Ast.term).
MetaCoq Quote Definition qMergeAnd := mergeAnd.
MetaCoq Quote Definition qMergeFormAnd := (fun a b => a∧b).
Definition reifyAnd : baseConnectiveReifier := fun lst _ envTerm env fPR => match lst with [x; y] => 
                                           xr <- fPR x 0 envTerm env;;yr <- fPR y 0 envTerm env;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                           ret (tApp qMergeFormAnd ([xt;yt]), tApp qMergeAnd ([envTerm;x;y;xt;yt;xp;yp])) | _ => fail "And applied to != 2 terms" end.
MetaCoq Quote Definition qMergeOr := mergeOr.
MetaCoq Quote Definition qMergeFormOr := (fun a b => a∨b).
Definition reifyOr  : baseConnectiveReifier := fun lst _ envTerm env fPR => match lst with [x; y] => 
                                           xr <- fPR x 0 envTerm env;;yr <- fPR y 0 envTerm env;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                           ret (tApp qMergeFormOr ([xt;yt]),tApp qMergeOr ([envTerm;x;y;xt;yt;xp;yp])) | _ => fail "Or applied to != 2 terms" end.
MetaCoq Quote Definition qMergeExists := mergeExists.
MetaCoq Quote Definition qMergeFormExists := (fun k => ∃k).
Definition reifyExist:baseConnectiveReifier := fun lst _ envTerm env fPR => match lst with [_; P] => 
                                           rr <- fPR P 1 envTerm env;; let '(rt,rp) := rr in 
                                           ret (tApp qMergeFormExists ([rt]), tApp qMergeExists ([envTerm;P;rt;rp])) | _ => fail "Exist applied to wrong terms" end.
MetaCoq Quote Definition qMergeEqProp := mergeEqProp.
Definition refiyCoqEq : baseConnectiveReifier := fun l fuel envTerm env fPR => match l with [tVar "D"; x; y] => 
                                           xr <- findTermRepresentation fuel x envTerm env ;;
                                           yr<- findTermRepresentation fuel y envTerm env ;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                           ret (tApp qMergeFormEq ([xt;yt]), tApp qMergeEqProp ([envTerm;x;y;xt;yt;xp;yp])) | _ => fail "Eq constructor applied to != 2 terms" end.
Definition reifyBase (s:string) : baseConnectiveReifier := match s with "and" => reifyAnd | "or" => reifyOr | "ex" => reifyExist | "eq" => refiyCoqEq | _ => fun _ _ _ _ _ => fail ("Unknown connective "++s) end.


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

Notation qProp := (tSort (Universe.from_kernel_repr (Level.lProp, false) nil)).

MetaCoq Quote Definition qnaryProp1 := Eval compute in (naryProp 1).
MetaCoq Quote Definition qexistT := @existT.
MetaCoq Quote Definition qiff := @iff.
MetaCoq Quote Definition qcong := @conj.

Definition abstractForall (t:Ast.term) : FailureMonad (Ast.term) :=
match t with tProd x t v =>
    let prop := tLambda x t v in
    ret (tLetIn (nNamed "Q") (tProd x t v) qProp (tApp (qexistT) ([qnaryProp1; tLambda (nNamed "P") qnaryProp1 (tApp qiff 
                ([tProd x (addRelIndex 0 2 t) (tApp (tRel 1) ([tRel 0])); tRel 1]));
                 addRelIndex 0 1 (prop); tApp qcong ([
tProd (nNamed "x") (tRel 0) (tRel 1);
tProd (nNamed "x") (tRel 0) (tRel 1);
tLambda (nNamed "k") (tRel 0) (tRel 0);
tLambda (nNamed "k") (tRel 0) (tRel 0)
])])))
| _ => fail "called abstractForall on something not a product" end.


Definition pred (n:nat) := match n with 0 => 0 | S n => n end.
Fixpoint flatten_monad {A:Type} (l:list (FailureMonad A)) : FailureMonad (list A) := match l with nil => ret nil | x::xr => xm <- x;; xrm <- flatten_monad xr;; ret (xm::xrm) end.
Definition map_monad {A B:Type} (f:A -> FailureMonad B) (l:list A) : FailureMonad (list B) := flatten_monad (map f l).
Definition map_def_monad {A B : Type} (tyf bodyf : A -> FailureMonad B) (d:def A) : FailureMonad (def B) := dtr <- tyf (dbody d);;dbr <- bodyf (dbody d);; ret {|
dname := dname d;
dtype := dtr;
dbody := dbr;
rarg := rarg d |}.

Fixpoint lowerRelIndex (minn:nat) (tv:FailureMonad Ast.term) (t:Ast.term) {struct t}: FailureMonad Ast.term := match t with
  tRel n => if Compare_dec.le_gt_dec minn n then if Compare_dec.le_gt_dec minn (S n) then ret (tRel (pred n)) else tv else ret (tRel n)
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

Definition appendZero (env:Ast.term -> FailureMonad nat) (zv:FailureMonad nat) : (Ast.term -> FailureMonad nat) := 
      fun (t:Ast.term) => match t with tRel n => (match n with 0 => zv | S n => env (tRel n) end) | _ => k <- lowerRelIndex 0 (fail "tRel 0 used when lowering") t;; (env k) end.
Definition appendAndLift (env:Ast.term -> FailureMonad nat) (zv:FailureMonad nat) : (Ast.term -> FailureMonad nat) := 
      fun t => match t with tRel n => (match n with 0 => zv | S n => k <- env (tRel n);;ret (S k) end) | _ => k <- lowerRelIndex 0 (fail "tRel 0 used when lowering") t;; v <- env k;;ret (S v) end.
Definition raiseEnvTermBase := (fun (d:D) (rho:nat -> D) => d .: rho).
MetaCoq Test Quote (fun (d:D) (rho:nat -> D) => d .: rho).
Definition qraiseEnvTerm := (tApp (tConst (MPfile (["FOL"; "Arith"]), "scons") nil) ([tVar "D"])).
Definition raiseEnvTerm (d:Ast.term) (env:Ast.term) : Ast.term := tApp (qraiseEnvTerm) ([d;env]).
(*
Axiom falsity : False.
Definition mergeFreeVarIntro (rho:nat -> D) (n:nat) (P:naryProp (S n)) 
                             (H:forall d:D, {phi:form & representsP phi (d.:rho) (P d)}) 
                             (*(H2:forall d:D, proj1 (H iO) = proj1 (H d))*) : {phi:form & representsP phi rho P}.
Proof.
pose (proj1 (H (iO))). exists f. exfalso. exact falsity.
(*intros k. destruct (H k) as [trm prf] eqn:Heq. specialize (H2 k). rewrite Heq in H2. cbn in H2. unfold f. rewrite H2. exact prf.*)
Defined.
Definition freeVarH2Proof (rho:nat -> D) (n:nat) (P:naryProp (S n)) (H:forall d:D, {phi:form & representsP phi (d.:rho) (P d)}) : forall d:D, proj1 (H d) = proj1 (H d).
Proof. intros d. exact eq_refl. Defined.
MetaCoq Quote Definition qVarIntro := mergeFreeVarIntro.
MetaCoq Quote Definition qH2Proof := freeVarH2Proof.
*)
MetaCoq Quote Definition qMergeFalse := mergeFalse.
MetaCoq Quote Definition qMergeForall := mergeForall.
MetaCoq Quote Definition qMergeImpl := mergeImpl.
MetaCoq Quote Definition qMergeFormFalse := fal.
MetaCoq Quote Definition qMergeFormForall := (fun k => ∀ k).
MetaCoq Quote Definition qMergeFormImpl := (fun p q => p --> q).
MetaCoq Quote Definition qform := form.
MetaCoq Quote Definition qenvType := (nat -> D).
MetaCoq Quote Definition qProj1 := @proj1.
MetaCoq Quote Definition qRepresentsP := @representsP.
MetaCoq Quote Definition qNaryProp := @naryProp.
MetaCoq Quote Definition qnat := nat.
Definition fvType := (fun (rho:nat -> D) (n:nat) (P:naryProp (S n)) =>  forall d:D, {phi:form & representsP phi (d.:rho) (P d)}).
MetaCoq Quote Definition qrepresentsT := fvType.

Fixpoint findPropRepresentation (fuel:nat) (t:Ast.term) (frees:nat) (envTerm:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (prod Ast.term Ast.term)) := 
let ffail :=fail ("Cannot represent form") in match fuel with 0 => fail "Out of fuel" | S fuel => 
  match (frees,t) with
  (0,(baseLogicConn "False" nil)) => ret (qMergeFormFalse, tApp qMergeFalse ([envTerm]))
| (0,(tApp (baseLogicConn name nil) lst)) => reifyBase name lst fuel envTerm env (findPropRepresentation fuel)
| (0,(tApp propConstructorBase lst)) => match popListStart lst termPropRepStart with
        Some (formRepDet i v) => vr <- recoverVector v;;reifyForm i vr fuel envTerm env (fun t => findPropRepresentation fuel t frees envTerm env)
      | _ => ffail end
| (0,tProd x P Q) => if Checker.eq_term init_graph P (tVar "D") then
                          k <- abstractForall (tProd x (tVar "D") Q);;
                          rQ <- findPropRepresentation fuel (tLambda x (tVar "D") Q) 1 envTerm env;; let '(tQ,pQ) := rQ in
                          ret (tApp qMergeFormForall ([tQ]), tApp qMergeForall ([envTerm;tProd x (tVar "D") Q;k;tQ;pQ]))
                     else
                          rP <- findPropRepresentation fuel P 0 envTerm env;;
                          Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                          rQ <- findPropRepresentation fuel Ql 0 envTerm env;; let '((tP,pP),(tQ,pQ)) := (rP,rQ) in
                          ret (tApp qMergeFormImpl ([tP;tQ]), tApp qMergeImpl ([envTerm;P;Ql;tP;tQ;pP;pQ]))
| (S n,tLambda x T P) => if Checker.eq_term init_graph T (tVar "D") then
      let envTermSub := raiseEnvTerm (tRel 0) (addRelIndex 0 1 envTerm) in
      let envSub := appendAndLift env (ret 0) in
      let num := quoteNumber n in
      k <- findPropRepresentation fuel P n envTermSub envSub;; let '(tk,pk) := k in
      ret (tk,(tLambda x (tVar "D") pk))
     else ffail
| _ => ffail end end.

Definition f2t {T:Type} (a:FailureMonad T) : TemplateMonad T := match a with ret k => monad_utils.ret k | fail s => tmFail s end.
Check existT.
Ltac representEnv env env2:= match goal with [ |- representableP ?n ?G ] =>
  let rep := fresh "rep" in let prf := fresh "prf" in let hyp := fresh "hyp" in let k y := (destruct y as [rep prf]) in
  (run_template_program (monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t (findPropRepresentation FUEL g n qe env2)) (fun '(tPq,pPq) => 
                         monad_utils.bind (tmUnquoteTyped (form) tPq) (fun tP:form => 
                         monad_utils.bind (tmUnquoteTyped (@representsP n tP env G) pPq) (fun tQ : @representsP n tP env G =>
                         monad_utils.ret (@existT form (fun mm => @representsP n mm env G) tP tQ))))))) k)
  ;exists rep;exists env;exact prf
end.
Ltac represent := representEnv (fun k:nat => iO) (fun (v:Ast.term) => @fail nat "unbound").

Goal (representableP 0 (iO i= iO)).
Time represent.
Qed.

Goal (representableP 0 (forall d:D, d i= iO)).
Time represent.
Show Proof.
Qed.

Goal (representableP 2 (fun a b  => a i= b)).
Time represent. 
Show Proof.
Qed.


Goal (representableP 2 (fun (d e :D) => forall g, exists j, g i= d i⊕ j /\ False -> False \/ (e i⊗ e i= iσ j /\ False))).
Time represent.
Show Proof.
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
Lemma test32 : (representableP 0 (forall a b c d e f g , a i= b i⊕ c i⊕ d i⊕ e i⊕ f i⊕ g)).
Time represent. 
Time Qed.
Set Printing Depth 500.
Print test32.

Goal forall n m:D, (representableP 0 (n i= m)).
intros n m. representEnv (fun k:nat => match k with 0 => n | _ => m end) (fun l:Ast.term => match l with (tVar "n") => ret 0 | (tVar "m") => ret 1 | _ => fail "unbound" end).
Qed.

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
    forall d n, n i⊕ (iσ d) = iσ (n i⊕ d).
  Proof.
    intros n. apply PAinduction.
    - representEnv (fun k:nat => n) (fun k:Ast.term => ret 0).
    - rewrite !add_zero; try reflexivity. all: firstorder.
    - intros d IH. rewrite !add_rec. now rewrite IH. all: firstorder.
  Qed.

End Models.