(** * Typing rules of the Pat programming language *)

From MailboxTypes Require Export Types.
From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Message.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.

Require Import Lists.List.
Import ListNotations.

Section typing_rules_def.

Generalizable All Variables.
Context `{M : IMessage Message}.
Context `{D : IDefinitionName DefinitionName}.

Inductive Member : TUsage -> Env -> Prop :=
  | Z : forall T env, Member T (Some T :: env)
  | S : forall T T' env, Member T env -> Member T (T' :: env).

(*lookup : {Γ : Context} → {n : ℕ} → (p : n ≺ (length Γ)) → Type*)
(*lookup {Γ , A} {zero} (s≤s z≤n) = A*)
(*lookup {Γ , A} {suc n} (s≤s p) = lookup p*)

Inductive Term' (prog : Prog) : Env -> TUsage -> Prop :=
  | VAR : forall env T, Member T env -> Term' prog env T
  | APP : forall env envList vList definition bodyType argumentTypes term,
      definitions prog definition = (FunDef definition argumentTypes bodyType term) ->
      [ envList ]+ₑ ~= env ->
      Forall3 (Term' prog) envList (map TValue vList) (argumentTypes) ->
      Term' prog env (TApp definition vList) bodyType
  .

Inductive WellTypedTerm (prog : Prog) : Env -> Term -> TUsage -> Prop :=
  (* Var *)
  | VAR   : forall v env T,
      SingletonEnv env ->
      lookup v env = Some T ->
      WellTypedTerm prog env (TValue (ValueVar (Var v))) T
  (* Consts *)
  | TRUE  : forall env,
      EmptyEnv env ->
      WellTypedTerm prog env (TValue (ValueBool true)) (TUBase BTBool)
  | FALSE : forall env,
      EmptyEnv env ->
      WellTypedTerm prog env (TValue (ValueBool false)) (TUBase BTBool)
  | UNIT  : forall env,
      EmptyEnv env ->
      WellTypedTerm prog env (TValue ValueUnit) (TUBase BTUnit)
  (* App *)
  | APP : forall env envList vList definition bodyType argumentTypes term,
      definitions prog definition = (FunDef definition argumentTypes bodyType term) ->
      [ envList ]+ₑ ~= env ->
      Forall3 (WellTypedTerm prog) envList (map TValue vList) (argumentTypes) ->
      WellTypedTerm prog env (TApp definition vList) bodyType
  (* Let *)
  | LET   : forall env env1 env2 T1 T2 t1 t2, 
      env1 ▷ₑ env2 ~= env ->
      WellTypedTerm prog env1 t1 ⌊ T1 ⌋ ->
      WellTypedTerm prog (Some ⌊ T1 ⌋ :: env2) t2 T2 ->
      WellTypedTerm prog env (TLet t1 t2) T2
  (* Spawn *)
  | SPAWN : forall env t,
      WellTypedTerm prog env t (TUBase BTUnit) ->
      WellTypedTerm prog ⌈ env ⌉ₑ (TSpawn t) (TUBase BTUnit)
  (* New *)
  | NEW : forall env,
      EmptyEnv env ->
      WellTypedTerm prog env TNew (? 𝟙 ^^ •)
  (* Send *)
  (* TODO: Maybe try a recursive approach with this rule *)
  | SEND : forall env env' envList tList vList m v,
      WellTypedTerm prog env' (TValue v) (! « m » ^^ ◦) ->
      signature prog m = tList ->
      [ (env' :: envList) ]+ₑ ~= env ->
      Forall3 (WellTypedTerm prog) envList (map TValue vList) (map secondType tList) ->
      WellTypedTerm prog env (TSend v m vList) (TUBase BTUnit)
  (* Guard *)
  | GUARD : forall env env1 env2 guards v T e f,
      env1 +ₑ env2 ~= env ->
      WellTypedTerm prog env1 (TValue v) (? f ^^ •) ->
      WellTypedGuards prog env2 guards T f ->
      e ⊑ f ->
      f ⊧ f ->
      WellTypedTerm prog env (TGuard v e guards) T
  (* Sub *)
  | SUB : forall t env1 env2 T1 T2,
      env1 ≤ₑ env2 ->
      T1 ≤ T2 ->
      WellTypedTerm prog env2 t T1 ->
      WellTypedTerm prog env1 t T2
with WellTypedGuards (prog : Prog) : Env -> list Guard -> TUsage -> MPattern -> Prop :=
  | SINGLE : forall T e env g,
      WellTypedGuard prog env g T e ->
      WellTypedGuards prog env (g :: nil) T e
  | SEQ : forall T e es env guards g,
      WellTypedGuard prog env g T e ->
      WellTypedGuards prog env guards T es ->
      WellTypedGuards prog env (g :: guards) T (e ⊕ es)
with WellTypedGuard (prog : Prog) : Env -> Guard -> TUsage -> MPattern -> Prop :=
  (* Fail *)
  | FAIL : forall t env, WellTypedGuard prog env GFail t 𝟘
  (* Free *)
  | FREE : forall t env T,
      WellTypedTerm prog env t T ->
      WellTypedGuard prog env (GFree t) T 𝟙
  (* Receive *)
  | RECEIVE : forall t m env T tList e mailbox,
      signature prog m = tList ->
      BaseTypes tList \/ BaseEnv env ->
      WellTypedTerm prog ((toEnv (map secondType tList)) ++ [Some (? e ^^ •)] ++ env) t T ->
      WellTypedGuard prog env (GReceive m mailbox t) T (« m » ⊙ e).

Inductive WellTypedDefinition (prog : Prog) : FunctionDefinition -> Prop :=
  | FUNDEF : forall defName argumentTypes body bodyType,
      WellTypedTerm prog (toEnv argumentTypes) body bodyType ->
      WellTypedDefinition prog (FunDef defName argumentTypes bodyType body).

Inductive WellTypedProgram (prog : Prog) : Prop :=
  PROG :
    (forall def, WellTypedDefinition prog (definitions prog def)) ->
    WellTypedTerm prog nil (initialTerm prog) (TUBase BTUnit) -> WellTypedProgram prog.

End typing_rules_def.

Section well_typed_def.

Generalizable All Variables.
Context `{M : IMessage Message}.
Context `{D : IDefinitionName DefinitionName}.

(*Definition EnvEqFV {T : TUsage} (p: Prog) (env : Env) (m : Term) : WellTypedTerm p env m T -> Prop.*)

End well_typed_def.
