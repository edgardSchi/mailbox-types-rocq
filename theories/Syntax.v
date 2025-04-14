(** * Syntax of the Pat programming language *)

From MailboxTypes Require Import Types.
From MailboxTypes Require Import Message.
From MailboxTypes Require Import Util.

Require Import Lists.List.

Generalizable All Variables.

Section syntax_def.

Context `{M : IMessage Message}.

(** We define a set of definition names to avoid dealing with
    function names. We assume they are defined before the
    program is executed.
*)
Class IDefinitionName DefinitionName : Type :=
  {
    eq_dec : forall m n, {@eq DefinitionName m n} + {~ @eq DefinitionName m n}
  }.

Context `{D : IDefinitionName DefinitionName}.

(** A variable is just a natural number *)
Inductive VarName : Type := Var : nat -> VarName.

(** We associated values as relations between environments and types.
    Since variables are treated as values, we need a way to check what
    their type is.
*)
Inductive Value : Type :=
    ValueBool : bool -> Value
  | ValueUnit : Value
  | ValueVar  : forall T env, Member T env -> Value.

Inductive Term : Type :=
    TValue : Value -> Term
  | TLet   : Term -> Term -> Term
  | TApp   : DefinitionName -> list Value -> Term
  | TSpawn : Term -> Term
  | TNew   : Term
  | TSend  : Value -> Message -> list Value -> Term
  | TGuard : Value -> list Guard -> Term
with Guard : Type :=
    GFail : Guard
  | GFree : Term -> Guard
  | GReceive : Message -> list VarName -> VarName -> Term -> Guard.



Inductive WellTypedTerm {f : Message -> list TType} : Env -> Term -> TUsage -> Prop :=
  (* Var *)
  (* Consts *)
  | TRUE  : WellTypedTerm nil (TValue (ValueBool true)) (TUBase BTBool)
  | FALSE : WellTypedTerm nil (TValue (ValueBool false)) (TUBase BTBool)
  | UNIT  : WellTypedTerm nil (TValue ValueUnit) (TUBase BTUnit)
  (* App *)
  | LET   : forall env env1 env2 T1 T2 t1 t2, 
      env1 ▷ₑ env2 ~= env ->
      WellTypedTerm env1 t1 ⌊ T1 ⌋ ->
      WellTypedTerm (cons ⌊ T1 ⌋ env2) t2 T2 ->
      WellTypedTerm env (TLet t1 t2) T2
  (* Spawn *)
  | SPAWN : forall env t,
      WellTypedTerm env t (TUBase BTUnit) ->
      WellTypedTerm ⌈ env ⌉ₑ (TSpawn t) (TUBase BTUnit)
  (* New *)
  | NEW : WellTypedTerm nil TNew (? 𝟙 ^^ •)
  (* Send *)
  (* TODO: Maybe try a recursive approach with this rule *)
  | SEND : forall env env' envList tList vList m v,
      WellTypedTerm env' (TValue v) (! « m » ^^ ◦) ->
      f m = tList ->
      [ (env' :: envList) ]+ₑ ~= env ->
      Forall3 WellTypedTerm envList (map TValue vList) (map secondType tList) ->
      WellTypedTerm env (TSend v m vList) (TUBase BTUnit)
  (* Guard TODO *)
  | GUARD : forall env env1 env2 guards v T e f,
      env1 +ₑ env2 ~= env ->
      WellTypedTerm env1 (TValue v) (? f ^^ •) ->
      WellTypedGuards env2 guards T f ->
      e ⊑ f ->
      (* TODO: Check if this is correct *)
      f ⊧ f ->
      WellTypedTerm env (TGuard v guards) T
  (* Sub *)
  | SUB : forall t env1 env2 T1 T2,
      env1 ≤ₑ env2 ->
      T1 ≤ T2 ->
      WellTypedTerm env2 t T1 ->
      WellTypedTerm env1 t T2
with WellTypedGuards {f : Message -> list TType} : Env -> list Guard -> TUsage -> MPattern -> Prop :=
  | SINGLE : forall T e env g,
      WellTypedGuard env g T e ->
      WellTypedGuards env (g :: nil) T e
  | SEQ : forall T e es env guards g,
      WellTypedGuard env g T e ->
      WellTypedGuards env guards T es ->
      WellTypedGuards env (g :: guards) T (e ⊕ es)
with WellTypedGuard {f : Message -> list TType} : Env -> Guard -> TUsage -> MPattern -> Prop :=
  (* Fail *)
  | FAIL : forall t env, WellTypedGuard env GFail t 𝟘
  (* Free *)
  | FREE : forall t env T, WellTypedTerm env t T -> WellTypedGuard env (GFree t) T 𝟙
  (* Receive *)
  | RECEIVE : forall t m env T tList vList e mailbox,
      f m = tList ->
      BaseTypes tList \/ BaseEnv env ->
      WellTypedTerm ((? e ^^ •) :: (map secondType tList) ++ env) t T ->
      (* TODO: Check if this makes sense with environments and variables *)
      WellTypedGuard env (GReceive m vList mailbox t) T (« m » ⊙ e).


(* Attempt at intrinsic typing. Kinda hard to work with *)
(*
Inductive WellTypedTerm {f : Message -> list TType}: Env -> TUsage -> Prop :=
  (* Var *)
  (* Consts *)
    TRUE  : WellTypedTerm nil (TUBase BTBool)
  | FALSE : WellTypedTerm nil (TUBase BTBool)
  (* App *)
  (* Let *)
  | LET   : forall env1 env2 env T1 T2,
      env1 ▷ₑ env2 ~= env ->
      WellTypedTerm env1 ⌊ T1 ⌋ ->
      WellTypedTerm (cons ⌊ T1 ⌋ env2) T2 ->
      WellTypedTerm env T2
  (* Spawn *)
  | SPAWN : forall env,
      WellTypedTerm env (TUBase BTUnit) ->
      WellTypedTerm ⌈ env ⌉ₑ (TUBase BTUnit)
  | NEW : WellTypedTerm nil (? 𝟙 ^^ •)
  (* New *)
  (* Send *)
  | SEND : forall env env' envList tList m,
      Value env' (! « m » ^^ ◦) ->
      f m = tList ->
      [ (env' :: envList) ]+ₑ ~= env ->
      WellTypedTerm env (TUBase BTUnit)
  (* Guard *)
  (* Sub *)
  | SUB : forall env1 env2 T1 T2,
      env1 ≤ₑ env2 ->
      T1 ≤ T2 ->
      WellTypedTerm env2 T1 ->
      WellTypedTerm env1 T2.
*)
End syntax_def.

Section Examples.

(* TODO: Add example from paper about future variable *)

End Examples.
