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
  (* Our monad for creating proper error messages *)
  Inductive FailureMonad (A:Type) : Type := ret : A -> FailureMonad A | fail : string -> FailureMonad A.
  Arguments ret {_} _.
  Arguments fail {_} _.
  Definition bind {A B : Type} (k:FailureMonad A) (f:A -> FailureMonad B) := match k return FailureMonad B with fail x => fail x | ret k => f k end.
  Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2)).
  Definition f2t {T:Type} (a:FailureMonad T) : TemplateMonad T := match a with ret k => monad_utils.ret k | fail s => tmFail s end.
  Fixpoint flatten_monad {A:Type} (l:list (FailureMonad A)) : FailureMonad (list A) := match l with nil => ret nil | x::xr => xm <- x;; xrm <- flatten_monad xr;; ret (xm::xrm) end.
  Definition map_monad {A B:Type} (f:A -> FailureMonad B) (l:list A) : FailureMonad (list B) := flatten_monad (map f l).
End FailureMonad.

Arguments ret {_} _.
Arguments fail {_} _.
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
  Fixpoint recoverVector (f : Ast.term) {struct f}: FailureMonad (list Ast.term) := let ffail := fail "not a vector application" in match f with
    vectorNil _ => ret nil
  | vectorCons x _ _ xr => xrl <- recoverVector xr;;ret (x::xrl)
  | _ => ffail
  end.

  (* General utils for quoted terms *)
  Existing Instance config.default_checker_flags.
  Fixpoint popNElements (l : list Ast.term) (n:nat) : option (list Ast.term) := match (l,n) with
    (a,0) => Some a
  | (x::xr, S n) => popNElements xr n
  | _ => None end.
  Fixpoint popListStart (l : list Ast.term) (ls : list Ast.term) : option (list Ast.term) := match (l,ls) with
    (a,nil)=> Some a
  | (lx::lxr, lsx::lsxr) => if Checker.eq_term init_graph lx lsx then popListStart lxr lsxr else None
  | _ => None end.
  MetaCoq Quote Definition qNatZero := 0.
  MetaCoq Quote Definition qNatSucc := S.
  MetaCoq Quote Definition qeq_refl := (@eq_refl).
  Fixpoint quoteNumber (n:nat) : Ast.term:= match n with 0 => qNatZero | S n => tApp qNatSucc ([quoteNumber n]) end.

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
  Class tarski_reflector := {
  fs : funcs_signature;
  ps : preds_signature;
  D  : Type;
  I  : @interp fs ps D;
  emptyEnv : nat -> D;
  isD : Ast.term -> bool
  }. 

  Context {tr : tarski_reflector}.
  Fixpoint naryProp (n:nat) : Type := match n with 0 => Prop | S nn => D -> naryProp nn end.
  Fixpoint representsP {n:nat} phi rho : (forall (P:naryProp n), Prop) := match n return (forall (P:naryProp n), Prop) with
       0  => (fun (P:Prop) => P <-> @sat fs ps D I rho phi)
    | S n => (fun (P:D -> naryProp n) => forall d, @representsP n phi (d.:rho) (P d)) end.
  Definition representableP (n:nat) (P : naryProp n) := exists phi rho, representsP phi rho P.
  Definition representsF (d:D) trm rho := @eval fs ps D I rho trm = d.
  Definition representableF (d:D) := exists trm rho, representsF d trm rho.

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
  MetaCoq Quote Definition qConstructTerm := constructTerm.
  MetaCoq Quote Definition qMergeTerm := mergeTerm.
  MetaCoq Quote Definition qConstructForm := constructForm.
  MetaCoq Quote Definition qMergeForm := mergeForm.

End AbstractReflectionDefinitions.

Section TarskiMerging.
  Context {tr : tarski_reflector}.
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

  Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
  Definition baseConnectiveReifier := Ast.term -> list Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> (Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad (prod Ast.term Ast.term))-> FailureMonad (prod Ast.term Ast.term).
  Definition reifyAnd : baseConnectiveReifier := fun tct lst _ envTerm env fPR => match lst with [x; y] => 
                                             xr <- fPR x 0 envTerm env;;yr <- fPR y 0 envTerm env;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                             ret (tApp qMergeFormAnd ([tct;xt;yt]), tApp qMergeAnd ([tct;envTerm;x;y;xt;yt;xp;yp])) | _ => fail "And applied to != 2 terms" end.
  Definition reifyOr  : baseConnectiveReifier := fun tct lst _ envTerm env fPR => match lst with [x; y] => 
                                             xr <- fPR x 0 envTerm env;;yr <- fPR y 0 envTerm env;; let '((xt,xp),(yt,yp)) := (xr,yr) in
                                             ret (tApp qMergeFormOr ([tct;xt;yt]),tApp qMergeOr ([tct;envTerm;x;y;xt;yt;xp;yp])) | _ => fail "Or applied to != 2 terms" end.
  Definition reifyExist:baseConnectiveReifier := fun tct lst _ envTerm env fPR => match lst with [_; P] => 
                                             rr <- fPR P 1 envTerm env;; let '(rt,rp) := rr in 
                                             ret (tApp qMergeFormExists ([tct;rt]), tApp qMergeExists ([tct;envTerm;P;rt;rp])) | _ => fail "Exist applied to wrong terms" end.
  Definition reifyBase (s:string) : baseConnectiveReifier := match s with "and" => reifyAnd | "or" => reifyOr | "ex" => reifyExist | _ => fun _ _ _ _ _ _ => fail ("Unknown connective "++s) end.

  Definition baseConnectiveReifierNP := Ast.term -> list Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> (Ast.term -> nat -> Ast.term -> (Ast.term -> FailureMonad nat) -> FailureMonad ( Ast.term))-> FailureMonad (Ast.term).
  Definition reifyAndNP : baseConnectiveReifierNP := fun tct lst _ envTerm env fPR => match lst with [x; y] => 
                                             xt <- fPR x 0 envTerm env;;yt <- fPR y 0 envTerm env;; 
                                             ret (tApp qMergeFormAnd ([tct;xt;yt])) | _ => fail "And applied to != 2 terms" end.
  Definition reifyOrNP  : baseConnectiveReifierNP := fun tct lst _ envTerm env fPR => match lst with [x; y] => 
                                             xt <- fPR x 0 envTerm env;;yt <- fPR y 0 envTerm env;; 
                                             ret (tApp qMergeFormOr ([tct;xt;yt])) | _ => fail "Or applied to != 2 terms" end.
  Definition reifyExistNP:baseConnectiveReifierNP := fun tct lst _ envTerm env fPR => match lst with [_; P] => 
                                             rt <- fPR P 1 envTerm env;;
                                             ret (tApp qMergeFormExists ([tct;rt])) | _ => fail "Exist applied to wrong terms" end.
  Definition reifyBaseNP (s:string) : baseConnectiveReifierNP := match s with "and" => reifyAndNP | "or" => reifyOrNP | "ex" => reifyExistNP | _ => fun _ _ _ _ _ _ => fail ("Unknown connective "++s) end.

End TarskiMerging.

Section ReificationHelpers.
  Definition termReifier := Ast.term -> list Ast.term -> Ast.term -> (Ast.term -> FailureMonad (prod Ast.term Ast.term)) -> FailureMonad (prod Ast.term Ast.term).
  Definition termReifierNP := Ast.term -> list Ast.term -> Ast.term -> (Ast.term -> FailureMonad (Ast.term)) -> FailureMonad (Ast.term).
  (* typeClassTerm -> vector of args -> env term -> recursion for arg vector -> prod (term, proof that term represents input *)
  Fixpoint applyRecursively (lt : list Ast.term) (IH : Ast.term -> FailureMonad (prod Ast.term Ast.term)) : FailureMonad (prod (list Ast.term) (list Ast.term)) :=
     match lt with nil => ret (nil,nil)
               | t::tr => IHt <- IH t;; atrIH <- applyRecursively tr IH;;let '(rep,prf) := IHt in let '(replist,fulllist) := atrIH in ret (rep::replist, rep::t::prf::fulllist) end.
  Fixpoint applyRecursivelyNP (lt : list Ast.term) (IH : Ast.term -> FailureMonad (Ast.term)) : FailureMonad ((list Ast.term) ) :=
     match lt with nil => ret (nil)
               | t::tr => rep <- IH t;; replist <- applyRecursivelyNP tr IH;;ret (rep::replist) end.
  Definition reifyTerm (c:Ast.term) : termReifier := fun tct av env IH => pr <- applyRecursively av IH;; let '(trm,fullarg) := pr in
                                                     ret (tApp qConstructTerm (tct::c::trm), tApp qMergeTerm (tct::c::env::fullarg)).
  Definition reifyForm (c:Ast.term) : termReifier := fun tct av env IH => pr <- applyRecursively av IH;; let '(trm,fullarg) := pr in
                                                     ret (tApp qConstructForm (tct::c::trm), tApp qMergeForm (tct::c::env::fullarg)).
  Definition reifyTermNP (c:Ast.term) : termReifierNP := fun tct av env IH => trm <- applyRecursivelyNP av IH;; 
                                                     ret (tApp qConstructTerm (tct::c::trm)).
  Definition reifyFormNP (c:Ast.term) : termReifierNP := fun tct av env IH => trm <- applyRecursivelyNP av IH;; 
                                                     ret (tApp qConstructForm (tct::c::trm)).
    
End ReificationHelpers.

Section EnvHelpers.
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
  Existing Instance config.default_checker_flags.
  MetaCoq Quote Definition qFs := @fs.
  MetaCoq Quote Definition qLocalVar := @var.
  MetaCoq Quote Definition qI_f := @i_f.
  MetaCoq Quote Definition qI_P := @i_P.

  Fixpoint findUBRecursively (lt : list Ast.term) (IH : Ast.term -> FailureMonad (list Ast.term)) : FailureMonad ((list Ast.term) ) :=
       match lt with nil => ret (nil)
                 | t::tr => rep <- IH t;; replist <- findUBRecursively tr IH;;ret (rep++replist) end.
  
  Fixpoint findUnboundVariablesTerm (fuel:nat) (t:Ast.term) {struct fuel}: (FailureMonad (list Ast.term)) := 
    let ffail := ret ([t]) in match fuel with 
      0 => fail "Out of fuel" 
      | S fuel => match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;findUBRecursively vr (findUnboundVariablesTerm fuel)
           | _ => ffail end else ffail
        | _ => ffail
      end 
    end.

    Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).
    Definition baseUBVarFinder := list Ast.term -> (Ast.term->nat->FailureMonad (list Ast.term)) -> FailureMonad (list Ast.term).
    Definition findUBAnd  :baseUBVarFinder := fun lst fPR => match lst with [x; y] => 
                                               xt <- fPR x 0;;yt <- fPR y 0;; 
                                               ret (xt++yt) | _ => fail "And applied to != 2 terms" end.
    Definition findUBOr   :baseUBVarFinder := fun lst fPR => match lst with [x; y] => 
                                               xt <- fPR x 0;;yt <- fPR y 0;; 
                                               ret (xt++yt) | _ => fail "Or applied to != 2 terms" end.
    Definition findUBExists:baseUBVarFinder := fun lst fPR => match lst with [_; P] => fPR P 1 | _ => fail "Exist applied to wrong terms" end.
    Definition findUBBase (s:string) : baseUBVarFinder := match s with "and" => findUBAnd | "or" => findUBOr | "ex" => findUBExists | _ => fun _ _ => fail ("Unknown connective "++s) end.

    Context {tr : tarski_reflector}.
    Definition maybeD : Ast.term -> Ast.term -> bool := fun tct mD => if @isD tr mD then true else Checker.eq_term init_graph mD (tApp qD ([tct])).
    Fixpoint findUnboundVariablesForm (tct:Ast.term) (fuel:nat) (t:Ast.term) (frees:nat) {struct fuel}: (FailureMonad (list Ast.term)) := 
    let ffail := fail ("Cannot introspect form " ++ string_of_term t) in match fuel with 0 => fail "Out of fuel" | S fuel => 
      match (frees,t) with
      (0,(baseLogicConn "False" nil)) => ret (nil)
    | (0,(tApp (baseLogicConn name nil) lst)) => findUBBase name lst (findUnboundVariablesForm tct fuel)
    | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
            Some ([fnc;v]) => vr <- recoverVector v;;findUBRecursively vr (fun t => findUnboundVariablesTerm fuel t)
          | _ => ffail end else ffail
    | (0,tProd x P Q) => if maybeD tct (P) then
                              findUnboundVariablesForm tct fuel (tLambda x P Q) 1
                         else
                              rP <- findUnboundVariablesForm tct fuel P 0;;
                              Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                              rQ <- findUnboundVariablesForm tct fuel Ql 0;;
                              ret (rP++rQ)
    | (S n,tLambda x T P) => if maybeD tct T then
          findUnboundVariablesForm tct fuel P n
         else ffail
    | _ => ffail end end.

   Fixpoint createEnvTerms (tct:Ast.term) (l:list Ast.term) (base:Ast.term) : prod (Ast.term) (Ast.term -> FailureMonad nat) := match l with 
         nil => (base,unboundEnv)
     | x::xr => let '(envTerm,env) := createEnvTerms tct xr base in (raiseEnvTerm tct x envTerm, fun a:Ast.term => if Checker.eq_term init_graph x a then ret 0 else v <- env a;;ret (S v)) end.


End EnvConstructor.

Section MainReificationFunctions.
  Existing Instance config.default_checker_flags.
  Fixpoint findTermRepresentation (tct:Ast.term) (fuel:nat) (t:Ast.term) (termEnv:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (prod Ast.term Ast.term)) := 
    let ffail := (envv <- env (t);;let num := quoteNumber (envv) in ret (tApp qLocalVar ([tApp qFs ([tct]);num]),tApp qeq_refl ([tApp qD ([tct]);t]))) in match fuel with 
      0 => fail "Out of fuel" 
      | S fuel => match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;reifyTerm fnc tct vr termEnv (fun t => findTermRepresentation tct fuel t termEnv env)
           | _ => ffail end else ffail
        | _ => ffail
      end 
    end.

  Fixpoint findTermRepresentationNP (tct:Ast.term) (fuel:nat) (t:Ast.term) (termEnv:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (Ast.term)) := 
    let ffail := (envv <- env (t);;let num := quoteNumber (envv) in ret (tApp qLocalVar ([tApp qFs ([tct]);num]))) in match fuel with 
      0 => fail "Out of fuel" 
      | S fuel => match t with
          tApp arg l => if Checker.eq_term init_graph arg qI_f then match popNElements l 4 with (*4 for funcs, preds, domain, interp *)
            Some ([fnc;v]) => vr <- recoverVector v;;reifyTermNP fnc tct vr termEnv (fun t => findTermRepresentationNP tct fuel t termEnv env)
           | _ => ffail end else ffail
        | _ => ffail
      end 
    end.

    Notation baseLogicConn x l:= (tInd {| inductive_mind := (MPfile (["Logic"; "Init"; "Coq"]), x); inductive_ind := 0 |} l).


    Context {tr : tarski_reflector}.
    Fixpoint findPropRepresentation (tct:Ast.term) (fuel:nat) (t:Ast.term) (frees:nat) (envTerm:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (prod Ast.term Ast.term)) := 
    let ffail :=fail ("Cannot represent form " ++ string_of_term t) in match fuel with 0 => fail "Out of fuel" | S fuel => 
      match (frees,t) with
      (0,(baseLogicConn "False" nil)) => ret (tApp qMergeFormFalse ([tct]), tApp qMergeFalse ([tct;envTerm]))
    | (0,(tApp (baseLogicConn name nil) lst)) => reifyBase name tct lst fuel envTerm env (findPropRepresentation tct fuel)
    | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
            Some ([fnc;v]) => vr <- recoverVector v;;reifyForm fnc tct vr envTerm (fun t => findTermRepresentation tct fuel t envTerm env)
          | _ => ffail end else ffail
    | (0,tProd x P Q) => if maybeD tct (P) then
                              rQ <- findPropRepresentation tct fuel (tLambda x P Q) 1 envTerm env;; let '(tQ,pQ) := rQ in
                              ret (tApp qMergeFormForall ([tct;tQ]), tApp qMergeForall ([tct;envTerm;tLambda x P Q;tQ;pQ]))
                         else
                              rP <- findPropRepresentation tct fuel P 0 envTerm env;;
                              Ql <- lowerRelIndex 0 (fail "Used var of implication precondition") Q;;
                              rQ <- findPropRepresentation tct fuel Ql 0 envTerm env;; let '((tP,pP),(tQ,pQ)) := (rP,rQ) in
                              ret (tApp qMergeFormImpl ([tct;tP;tQ]), tApp qMergeImpl ([tct;envTerm;P;Ql;tP;tQ;pP;pQ]))
    | (S n,tLambda x T P) => if maybeD tct T then
          let envTermSub := raiseEnvTerm tct (tRel 0) (addRelIndex 0 1 envTerm) in
          let envSub := appendAndLift env (ret 0) in
          k <- findPropRepresentation tct fuel P n envTermSub envSub;; let '(tk,pk) := k in
          ret (tk,(tLambda x (tApp qD ([tct])) pk))
         else ffail
    | _ => ffail end end.

    Fixpoint findPropRepresentationNP (tct:Ast.term) (fuel:nat) (t:Ast.term) (frees:nat) (envTerm:Ast.term) (env:Ast.term -> FailureMonad nat) {struct fuel}: (FailureMonad (Ast.term)) := 
    let ffail :=fail ("Cannot represent form " ++ string_of_term t) in match fuel with 0 => fail "Out of fuel" | S fuel => 
      match (frees,t) with
      (0,(baseLogicConn "False" nil)) => ret (tApp qMergeFormFalse ([tct]))
    | (0,(tApp (baseLogicConn name nil) lst)) => reifyBaseNP name tct lst fuel envTerm env (findPropRepresentationNP tct fuel)
    | (0,(tApp arg lst)) => if Checker.eq_term init_graph arg qI_P then match popNElements lst 4 with
            Some ([fnc;v]) => vr <- recoverVector v;;reifyFormNP fnc tct vr envTerm (fun t => findTermRepresentationNP tct fuel t envTerm env)
          | _ => ffail end else ffail
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


Definition FUEL := 100. 
Ltac representEnvP env1 env2:= 
match goal with [ |- @representableP ?i ?n ?G ] =>
  let rep := fresh "rep" in let prf := fresh "prf" in let env := fresh "env" in let k y := (destruct y as [rep prf]) in
  pose ((match env1 with None => @emptyEnv i | Some kk => kk end)) as env;
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t (@findPropRepresentation i tct FUEL g n qe env2)) (fun '(tPq,pPq) => 
                         monad_utils.bind (tmUnquoteTyped (form) tPq) (fun tP:form => 
                         monad_utils.bind (tmUnquoteTyped (@representsP i n tP env G) pPq) (fun tQ : @representsP i n tP env G =>
                         monad_utils.ret (@existT form (fun mm => @representsP i n mm env G) tP tQ)))))))) k)
  ;exists rep;exists env;exact prf 
end.


Ltac representEnvPNP env1 env2:= 
match goal with [ |- @representableP ?i ?n ?G ] =>
  let rep := fresh "rep" in let prf := fresh "prf" in let env := fresh "env" in let k y := (pose y as rep) in
  pose ((match env1 with None => @emptyEnv i | Some kk => kk end)) as env;
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmQuote env) (fun qe => 
                         monad_utils.bind (f2t ((@findPropRepresentationNP i tct FUEL g n qe env2))) (fun tPq => 
                         monad_utils.bind (tmUnquoteTyped (form) tPq) (fun tP:form => 
                         monad_utils.ret (tP))))))) k)
  ;exists rep;exists env;easy 
end.
Ltac represent := match goal with [ |- @representableP ?i ?n ?G ] => representEnvP (@None(nat -> @D i)) unboundEnv end.
Ltac representNP := match goal with [ |- @representableP ?i ?n ?G ] => representEnvPNP (@None(nat -> @D i)) unboundEnv end.

Ltac constructEnv := 
match goal with [ |- @representableP ?i ?n ?G ] => (*(pose (fst y) as envBase;pose (snd y) as envTerm*)
  let envBase := fresh "envBase" in let envTerm := fresh "envTerm" in let k y := (pose (fst y) as envBase;pose (snd y) as envTerm) in
  (run_template_program (monad_utils.bind (tmQuote i) (fun tct =>
                         monad_utils.bind (tmQuote G) (fun g => 
                         monad_utils.bind (tmQuote (@emptyEnv i)) (fun baseEnv => 
                         monad_utils.bind (f2t ((@findUnboundVariablesForm i tct FUEL g n))) (fun lst => 
                         let '(envToDR,envToNat) := (createEnvTerms tct lst baseEnv) in
                         monad_utils.bind (tmUnquoteTyped (nat -> @D i) envToDR) (fun envToD => 
                         monad_utils.ret (pair envToD envToNat))))))) k)
end.

