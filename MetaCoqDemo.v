(*
                             ...          ...
                              |            /\
                    parsing   |            | printing
                              |            |
                              V            |
                       intf/Constrexpr.constr_expr
                              |            /\
                 constrintern |            | constrextern
                  (in interp) |            | (in interp)
                globalization |            |
                              V            |
                           Glob_term.glob_constr
                              |            /\
                    pretyping |            | detyping
                              |            | (in pretyping)
                              V            |
                               Term.constr
                                 |     /\
                   safe_typing   |      |
                   (validation   |      |
                      by kernel) |______|

  coq/kernel/constr.ml

*)


From MetaCoq.Template Require Import utils All.
Require Import List String.
Import MonadNotation.
Import ListNotations.
Open Scope string_scope.

(** * The term type  *)

Print Ast.term.

(** * Quoting and unquoting  *)

MetaCoq Test Quote (fun x : nat => x).

MetaCoq Test Quote (fun (f : nat -> nat) (x : nat) => f x).

MetaCoq Test Quote (let x := 2 in x).

MetaCoq Test Quote (let x := 2 in
            match x with
              | 0 => 0
              | S n => n
            end).

MetaCoq Test Quote 0.
MetaCoq Test Unquote (Ast.tConstruct (mkInd (MPfile ["Datatypes"; "Init"; "Coq"], "nat") 0) 1 []).

(** Fixpoints **)
Fixpoint add (a b : nat) : nat :=
  match a with
    | 0 => b
    | S a => S (add a b)
  end.
Eval vm_compute in add.

MetaCoq Test Quote add.

Fixpoint add' (a b : nat) : nat :=
  match b with
    | 0 => a
    | S b => S (add' a b)
  end.

Fixpoint even (a : nat) : bool :=
  match a with
    | 0 => true
    | S a => odd a
  end
with odd (a : nat) : bool :=
  match a with
    | 0 => false
    | S a => even a
  end.

MetaCoq Quote Definition add_syntax := Eval compute in add.
Print add_syntax.
MetaCoq Quote Recursively Definition add_prog := add.
Print add_prog.

MetaCoq Quote Definition eo_syntax := Eval compute in even.

MetaCoq Quote Definition add'_syntax := Eval compute in add'.

MetaCoq Unquote Definition t := add_syntax.
Print t.

(** * Example function: Unfolding constants *)

Fixpoint unfold_consts (Σ : global_env) (t : term) :=
  match t with
  | tRel i => tRel i
  | tEvar ev args => tEvar ev (List.map (unfold_consts Σ ) args)
  | tLambda na T M => tLambda na (unfold_consts Σ  T) (unfold_consts Σ  M)
  | tApp u v => tApp (unfold_consts Σ  u) (List.map (unfold_consts Σ ) v)
  | tProd na A B => tProd na (unfold_consts Σ  A) (unfold_consts Σ  B)
  | tCast C kind t => tCast (unfold_consts Σ  C) kind (unfold_consts Σ  t)
  | tLetIn na b t b' => tLetIn na (unfold_consts Σ  b) (unfold_consts Σ  t) (unfold_consts Σ  b')
  | tCase ind p C brs =>
    let brs' := List.map (on_snd (unfold_consts Σ )) brs in
    tCase ind (unfold_consts Σ  p) (unfold_consts Σ  C) brs'
  | tProj p C => tProj p (unfold_consts Σ  C)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (unfold_consts Σ ) (unfold_consts Σ )) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (unfold_consts Σ ) (unfold_consts Σ )) mfix in
    tCoFix mfix' idx
  | tConst name u => match lookup_env Σ name with
                    | Some (ConstantDecl (Build_constant_body _ (Some body) u)) => body
                    | _ => tConst name u
                    end
  | x => x
  end.

Fixpoint unfold_consts_env (Σ : global_env) :=
  match Σ with
    (na , ConstantDecl cnst) :: Σ =>
    let Σ' := unfold_consts_env Σ in
    ((na, ConstantDecl (map_constant_body (unfold_consts Σ') cnst))) :: Σ'
  | c :: Σ => c :: unfold_consts_env Σ
  | [] => []
  end.

Definition two := 2.
Lemma three : nat. exact (1 + two). Qed.

MetaCoq Quote Recursively Definition bla := three.

Definition Σ := fst bla.

Compute Σ.
Check Σ.
Print add.
MetaCoq Test Unquote (tConstruct
                                 {|
                                 inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat");
                                 inductive_ind := 0 |} 1 []).
Definition ter := snd bla.
Compute ter.

Definition ter' :=let Σ' := unfold_consts_env Σ in
         let ter' := unfold_consts Σ' ter in
         ter'.
Compute ter'.

MetaCoq Unquote Definition def := ter'.
Print def.

Definition unfoldAllConsts {A} (a : A) :=
  pair <- tmQuoteRec a ;;
  let Σ' := fst pair in
  let t' := snd pair in
  let Σ := unfold_consts_env Σ' in
  let t := unfold_consts Σ t' in
  tmUnquoteTyped A t.

Definition unfoldAllConstsDef {A} (na : string) (a : A) :=
  res <- unfoldAllConsts a ;;
  tmDefinition na res.

MetaCoq Run (res <- unfoldAllConsts three ;; tmPrint res).

MetaCoq Run (unfoldAllConstsDef "three_transp" three).
Print three_transp.

(** ** Unfolding and reducing constants *)

From MetaCoq Require Import Checker.All.
Require Import String List.
Open Scope string_scope.

Definition FUEL := 100.

Definition reduce Σ t := match reduce_opt RedFlags.default Σ [] FUEL t with Some res => res | _ => tVar "noresult" end.

Fixpoint unfold_consts_red (Σ : global_env) (t : term) :=
  match t with
  | tRel i => tRel i
  | tEvar ev args => tEvar ev (List.map (unfold_consts_red Σ ) args)
  | tLambda na T M => tLambda na (unfold_consts_red Σ  T) (unfold_consts_red Σ  M)
  | tApp u v => tApp (unfold_consts_red Σ  u) (List.map (unfold_consts_red Σ ) v)
  | tProd na A B => tProd na (unfold_consts_red Σ  A) (unfold_consts_red Σ  B)
  | tCast C kind t => tCast (unfold_consts_red Σ  C) kind (unfold_consts_red Σ  t)
  | tLetIn na b t b' => tLetIn na (unfold_consts_red Σ  b) (unfold_consts_red Σ  t) (unfold_consts_red Σ  b')
  | tCase ind p C brs =>
    let brs' := List.map (on_snd (unfold_consts_red Σ )) brs in
    tCase ind (unfold_consts_red Σ  p) (unfold_consts_red Σ  C) brs'
  | tProj p C => tProj p (unfold_consts_red Σ  C)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (unfold_consts_red Σ ) (unfold_consts_red Σ )) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (unfold_consts_red Σ ) (unfold_consts_red Σ )) mfix in
    tCoFix mfix' idx
  | tConst name u => match lookup_env Σ name with
                    | Some (ConstantDecl (Build_constant_body _ (Some body) u)) => reduce Σ body
                    | _ => tConst name u
                    end
  | x => x
  end.

Fixpoint unfold_consts_red_env (Σ : global_env) :=
  match Σ with
    (na , ConstantDecl cnst) :: Σ =>
    let Σ' := unfold_consts_red_env Σ in
    ((na, ConstantDecl (map_constant_body (unfold_consts_red Σ') cnst))) :: Σ'
  | c :: Σ => c :: unfold_consts_red_env Σ
  | [] => []
  end.

Definition makeTransparent_red {A} (a : A) :=
  mlet (Σ', t') <- tmQuoteRec a ;;
  let Σ := unfold_consts_red_env Σ' in
  let t := unfold_consts_red Σ t' in
  tmUnquoteTyped A t.

Definition makeTransparentDef_red {A} (na : string) (a : A) :=
  res <- makeTransparent_red a ;;
  tmDefinition na res.
MetaCoq Run (res <- makeTransparent_red three ;; tmPrint res).
MetaCoq Run (makeTransparentDef_red "three_transp_red" (1 + three)).
Print three_transp_red.

(** ** Unfolding all constants, reducing propositional constants *)

Existing Instance config.default_checker_flags.

Fixpoint unfold_consts_red_prop (Σ : global_env) (t : term) :=
  match t with
  | tRel i => tRel i
  | tEvar ev args => tEvar ev (List.map (unfold_consts_red_prop Σ ) args)
  | tLambda na T M => tLambda na (unfold_consts_red_prop Σ  T) (unfold_consts_red_prop Σ  M)
  | tApp u v => tApp (unfold_consts_red_prop Σ  u) (List.map (unfold_consts_red_prop Σ ) v)
  | tProd na A B => tProd na (unfold_consts_red_prop Σ  A) (unfold_consts_red_prop Σ  B)
  | tCast C kind t => tCast (unfold_consts_red_prop Σ  C) kind (unfold_consts_red_prop Σ  t)
  | tLetIn na b t b' => tLetIn na (unfold_consts_red_prop Σ  b) (unfold_consts_red_prop Σ  t) (unfold_consts_red_prop Σ  b')
  | tCase ind p C brs =>
    let brs' := List.map (on_snd (unfold_consts_red_prop Σ )) brs in
    tCase ind (unfold_consts_red_prop Σ  p) (unfold_consts_red_prop Σ  C) brs'
  | tProj p C => tProj p (unfold_consts_red_prop Σ  C)
  | tFix mfix idx =>
    let mfix' := List.map (map_def (unfold_consts_red_prop Σ ) (unfold_consts_red_prop Σ )) mfix in
    tFix mfix' idx
  | tCoFix mfix idx =>
    let mfix' := List.map (map_def (unfold_consts_red_prop Σ ) (unfold_consts_red_prop Σ )) mfix in
    tCoFix mfix' idx
  | tConst name u => match lookup_env Σ name with
                    | Some (ConstantDecl (Build_constant_body _ (Some body) u)) =>
                      match infer (F := FUEL) Σ init_graph [] body with
                      | Checked (tSort s) => if Universe.is_prop s then reduce Σ body else body
                      | _ => body
                      end
                    | _ => tConst name u
                    end
  | x => x
  end.

Fixpoint unfold_consts_red_prop_env (Σ : global_env) :=
  match Σ with
    (na , ConstantDecl cnst) :: Σ =>
    let Σ' := unfold_consts_red_prop_env Σ in
    ((na, ConstantDecl (map_constant_body (unfold_consts_red_prop Σ') cnst))) :: Σ'
  | c :: Σ => c :: unfold_consts_red_prop_env Σ
  | [] => []
  end.

Definition makeTransparent_red_prop {A} (a : A) :=
  mlet (Σ', t') <- tmQuoteRec a ;;
  let Σ := unfold_consts_red_prop_env Σ' in
  let t := unfold_consts_red_prop Σ t' in
  tmUnquoteTyped A t.

Definition makeTransparentDef_red_prop {A} (na : string) (a : A) :=
  res <- makeTransparent_red_prop a ;;
  tmDefinition na res.

MetaCoq Run (res <- makeTransparent_red_prop three ;; tmPrint res).

Definition cst : Prop. Proof. exact ((fun x : Prop => x) True). Qed.

Definition four : nat.
  exact (fst (1 + three, cst)).
Qed.
MetaCoq Run (makeTransparent_red_prop four >>= tmPrint).

(** * The Template Monad  *)

Print TemplateMonad.

Local Notation Nat_module := (MPfile ["Datatypes"; "Init"; "Coq"], "nat").
Notation inat :=
  {| inductive_mind := Nat_module; inductive_ind := 0 |}.

MetaCoq Run (t <- tmQuote (3 + 3) ;; tmPrint t).

MetaCoq Run (t <- tmQuoteRec add ;; tmPrint t ).

Locate add.
MetaCoq Run (t <- tmLocate "add" ;; tmPrint t).

Definition printInductive (q : qualid): TemplateMonad unit :=
  kn <- tmLocate1 q ;;
  match kn with
  | IndRef ind => (tmQuoteInductive ind.(inductive_mind)) >>= tmPrint
  | _ => tmFail ("[" ++ q ++ "] is not an inductive")
  end.

MetaCoq Run (printInductive "Coq.Init.Datatypes.nat").
MetaCoq Run (printInductive "nat").
Fail MetaCoq Run (printInductive "natt").
Fail MetaCoq Run (printInductive "S").

MetaCoq Run (tmDefinition "foo" nat >>= tmPrint).
Compute foo.

MetaCoq Run (t <- tmDefinition "foo5'" 12 ;;
                     tmDefinition "foo6'" t).
Print foo5'.
Print foo6'.

MetaCoq Run (tmLemma "foo51" nat ;;
                     tmLemma "foo61" bool).
Next Obligation.
  exact 3.
Defined.
Next Obligation.
  exact true.
Qed.
Compute foo51.
Compute foo61.

MetaCoq Run (tmAxiom "fal" False).

(** * PCUIC  *)

Print term.

Require Import MetaCoq.PCUIC.PCUICAst MetaCoq.PCUIC.PCUICTyping. 

Print term.
Print typing.

Require Import MetaCoq.PCUIC.PCUICSR MetaCoq.PCUIC.PCUICConfluence MetaCoq.PCUIC.PCUICValidity.

(* Ex 0 (challenge):
   Write down the right correctness lemma, and then try to prove it.
   Lemma unfold_correct : *)
(*
Σ ;;; Γ |- t : T ->
Σ ;;; Γ |- t ->* unfold_consts (unfold_consts_env Σ) t : T. *)


(** * Running in tactics  *)

Goal forall n, n > 0 -> exists m, m < 0.
Proof.
  Time match goal with [ |- ?G ] =>
  let k y := idtac y in
  run_template_program (tmQuote G) k
  end.
Abort.

(** * Extraction to OCaml  *)

Extraction mult.

Lemma test : forall x, { y | y > 2 * x}.
Proof.
  intros x. exists (2 * x + 1). lia.
Defined.

Extraction test.

(** * Erasure  *)

Require MetaCoq.Erasure.EAst MetaCoq.Erasure.ErasureFunction.

Print EAst.term.
Print ErasureFunction.erase.

(** * Type-checking and erasure  *)

From MetaCoq.Template Require Import Loader.
From MetaCoq.Erasure Require Import Loader.
From MetaCoq.SafeChecker Require Import Loader.

MetaCoq SafeCheck nat.
MetaCoq SafeCheck (forall X : Prop, Prop).
MetaCoq SafeCheck 0.

MetaCoq Erase nat.

MetaCoq Erase I.
MetaCoq Erase true.

MetaCoq Erase (@exist nat (fun x => x = 0) 0 (eq_refl) : {x : nat | x = 0}).

MetaCoq Erase (ltac:(let x := eval unfold test in test in exact x)).

(*
  Ex 1: MetaCoq. Write a function which normalizes all propositional subterms (have type Prop). Then write a function which normalizes all subterms which are proofs.
*)

(*
  Ex 2: Reflection using Metacoq. Write a reflection function like on day 2 for the simplification of propositional proof goals, this time with MetaCoq.
*)

(*
 Ex 3: Extraction.

  1. Define inductively a relation Fib which specifies the fibonnaci function (fib 0=0 fib 1=1 fib (n+2)=fib n+fib (n+1)) as a binary relation.
  2. Prove the following principle by one simple induction: ∀ P:nat→Type, P 0 → P 1 → (∀ n, P n → P (S n) → P (S (S n))) → ∀ n,P n
  3. Use this principle in order to prove ∀ n, {m|Fib n m}
  4. Look at the extracted program, what is its complexity ?
  5. Propose another proof of the induction principle using the Fixpoint construction, compare the programs obtained. 

*)

(*
 Ex (challenge): Write down a correctness statement for the reflection function

 Something along the lines of

  MetaCoq Quote Definition eval_syntax := eval.
  Definition eval_ := trans eval.

  MetaCoq Quote Definition eval_syntax := eval.
  Definition eval_ := trans eval.

  Σ ;;; Γ |- p : tSort u ->
  is_prop u ->
  reflect p = Some r ->
  exists prf, Σ ;;; Γ |- prf : mkApps eq_ [tApp eval_ r ; p]

 *)
