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

Inductive Term' (prog : Prog) (env : Env) : TUsage -> Prop :=
  | VAR : forall T, Member T env -> Term' prog env T
  (*| APP : forall v definition bodyType argumentType term,*)
  (*    definitions prog definition = (FunDef definition argumentType bodyType term) ->*)
  (*    Term' prog env (TValue v) argumentType ->*)
  (*    Term' prog env (TApp definition v) bodyType*)
  | LET : forall env1 env2 T1 T2,
      env1 ▷ₑ env2 ~= env ->
      Term' prog env1 ⌊ T1 ⌋ ->
      Term' prog (Some ⌊ T1 ⌋ :: env2) T2 ->
      Term' prog env T2
  | NEW : EmptyEnv env -> Term' prog env (? 𝟙 ^^ •)
  | SUB : forall env' T1 T2,
      env ≤ₑ env' ->
      T1 ≤ T2 ->
      Term' prog env' T1 ->
      Term' prog env T2
with Guards' (prog : Prog) (env : Env) : TUsage -> MPattern -> Prop :=
  | SINGLE : forall T e,
      Guard' prog env T e ->
      Guards' prog env T e
  | SEQ : forall T e es,
      Guard' prog env T e ->
      Guards' prog env T es ->
      Guards' prog env T (e ⊕ es)
with Guard' (prog : Prog) (env : Env) : TUsage -> MPattern -> Prop :=
  | FAIL : forall T, Guard' prog env T 𝟘
  | FREE : forall T, Term' prog env T -> Guard' prog env T 𝟙
  | RECEIVE : forall m T T' e,
      signature prog m = T' ->
      BaseType T' \/ BaseEnv env ->
      Term' prog (Some (secondType T') :: Some (? e ^^ •) :: env) T ->
      Guard' prog env T (« m » ⊙ e).

End typing_rules_def.
