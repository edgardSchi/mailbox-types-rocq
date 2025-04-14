(** * Syntax of types *)

Require Import Lia.

From MailboxTypes Require Import Message.
From MailboxTypes Require Export MailboxPatterns.

Require Import List.
Import ListNotations.

Generalizable All Variables.

Section type_def.

Context `{M : IMessage Message}.

(** Mailbox type definition *)
Inductive MType `{IMessage Message} : Type :=
    MTOutput : MPattern -> MType
  | MTInput  : MPattern -> MType.

(** Base type definition. For now only unit type and booleans *)
Inductive BType : Type :=
    BTUnit : BType
  | BTBool : BType.

(** Type definition. A type is either a base type or a mailbox type *)
Inductive TType : Type :=
    TTBase : BType -> TType
  | TTMailbox : MType -> TType.

(** Usage annotation for quasi-linear typing *)
Inductive UsageAnnotation : Type :=
    SecondClass
  | Returnable.

(** Quasi-linear types are types equipped with a usage annotation.
    Base types have no restrictions. Mailbox types are either second class
   or returnable.
*)
Inductive TUsage : Type :=
    TUBase : BType -> TUsage
  | TUUsage : UsageAnnotation -> MType -> TUsage.

Definition returnType (t : TType) : TUsage :=
  match t with
  | TTBase b => TUBase b
  | TTMailbox m => TUUsage Returnable m
  end.

Definition returnUsage (t : TUsage) : TUsage :=
  match t with
  | TUBase b => TUBase b
  | TUUsage _ m => TUUsage Returnable m
  end.

Definition secondType (t : TType) : TUsage :=
  match t with
  | TTBase b => TUBase b
  | TTMailbox m => TUUsage SecondClass m
  end.

Definition secondUsage (t : TUsage) : TUsage :=
  match t with
  | TUBase b => TUBase b
  | TUUsage _ m => TUUsage SecondClass m
  end.


(** A list of only base types *)
Fixpoint BaseTypes (e : list TType) : Prop :=
  match e with
  | nil => True
  | (TTBase _ :: e') => BaseTypes e'
  | _ => False
  end.

Inductive UsageSubtype : UsageAnnotation -> UsageAnnotation -> Prop :=
    UsageSubtypeRefl : forall n, UsageSubtype n n
  | UsageSubtypeLe   : UsageSubtype Returnable SecondClass.

Inductive Subtype : TUsage -> TUsage -> Prop :=
    SubtypeBase : forall c, Subtype (TUBase c) (TUBase c)
  | SubtypeInput : forall e f n1 n2,
      MPInclusion e f -> UsageSubtype n1 n2 -> Subtype (TUUsage n1 (MTInput e)) (TUUsage n2 (MTInput f))
  | SubtypeOutput : forall e f n1 n2,
      MPInclusion f e -> UsageSubtype n1 n2 -> Subtype (TUUsage n1 (MTOutput e)) (TUUsage n2 (MTOutput f)).

Definition TypeEqual (a b : TUsage) : Prop :=
  Subtype a b /\ Subtype b a.

End type_def.

(** ** Notation for types *)
Declare Scope types_scope.
Open Scope types_scope.

Notation "! E" := (MTOutput E) (at level 73) : types_scope.
Notation "? E" := (MTInput E) (at level 73) : types_scope.
Notation "◦" := (SecondClass) : types_scope.
Notation "•" := (Returnable) : types_scope.
Notation "T ^^ n" := (TUUsage n T) (at level 75) : types_scope.
Notation "⌊ T ⌋" := (returnType T) : types_scope.
Notation "⌊ T ⌋ⁿ" := (returnUsage T) : types_scope.
Notation "⌈ T ⌉" := (secondType T) : types_scope.
Notation "⌈ T ⌉ⁿ" := (secondUsage T) : types_scope.
Notation "n1 ≤ⁿ n2" := (UsageSubtype n1 n2) (at level 80) : types_scope.
Notation "A ≤ B" := (Subtype A B) (at level 80) : types_scope.
Notation "A ≃ B" := (TypeEqual A B) (at level 80) : types_scope.

Section mailbox_types_classes.

Context `{M : IMessage Message}.

(* TODO: Check if this is correct *)
Definition Relevant (m : MType) : Prop :=
  forall n, ~ ((TUUsage n m) ≤ (TUUsage n (! 𝟙))).

Definition Irrelevant (m : MType) : Prop :=
  ~ Relevant m.

Definition Reliable (m : MType) : Prop :=
  forall n, ~ ((TUUsage n m) ≤ (TUUsage n (? 𝟘))).

Definition Unreliable (m : MType) : Prop :=
  ~ Reliable m.

Definition Usable (m : MType) : Prop :=
  forall n, ~ ((TUUsage n m) ≤ (TUUsage n (! 𝟘))).

Definition Unusable (m : MType) : Prop :=
  ~ Usable m.

(* TODO: Check if this is correct *)
Inductive Unrestricted : TUsage -> Prop :=
    unBase : forall c : BType, Unrestricted (TUBase c)
  | unOne : Unrestricted (TUUsage SecondClass (! 𝟙)).

Definition Linear (m : TUsage) : Prop :=
  ~ Unrestricted m.

End mailbox_types_classes.

Section mailbox_combinations.

  Context `{M : IMessage Message}.
(** 
   Definition 3.5 of type combiniations. Instead of defining it as a partial function,
   we define it as a relation between three types.
*)
  Inductive TypeCombination : TType -> TType -> TType -> Prop :=
      TCombBase : forall c, TypeCombination (TTBase c) (TTBase c) (TTBase c)
    | TCombOut : forall e f, TypeCombination (TTMailbox (! e)) (TTMailbox (! f)) (TTMailbox (! (e ⊙ f)))
    | TCombInOut : forall e f, TypeCombination (TTMailbox (! e)) (TTMailbox (? (e ⊙ f))) (TTMailbox (? f))
    | TCombOutIn : forall e f, TypeCombination (TTMailbox (? (e ⊙ f))) (TTMailbox (! e)) (TTMailbox (? f)).

(** 
   Definition 3.6 of usage combiniations. Again, instead of defining it as a partial function,
   we define it as a relation between three usage annotations.
*)
  Inductive UsageCombination : UsageAnnotation -> UsageAnnotation -> UsageAnnotation -> Prop :=
      UCombSecond : UsageCombination SecondClass SecondClass SecondClass
    | UCombSecRet : UsageCombination SecondClass Returnable Returnable.

(** 
   Definition 3.7 of usage-annotated type combiniations.
   Again, instead of defining it as a partial function,
   we define it as a relation between three types.
*)
  Inductive TypeUsageCombination : TUsage -> TUsage -> TUsage -> Prop :=
      TUsageCombBase : forall c, TypeUsageCombination (TUBase c) (TUBase c) (TUBase c)
    | TUsageCombUsage : forall j k n1 n2 n t,
        UsageCombination n1 n2 n ->
        TypeCombination (TTMailbox j) (TTMailbox k) (TTMailbox t) ->
        TypeUsageCombination (TUUsage n1 j) (TUUsage n2 k) (TUUsage n t).
End mailbox_combinations.

Notation "T ⊞ U ~= V" := (TypeCombination T U V) (at level 80) : types_scope.
Notation "n1 ▷ⁿ n2 ~= n" := (UsageCombination n1 n2 n) (at level 80) : types_scope.
Notation "J ▷ K ~= L" := (TypeUsageCombination K J L) (at level 80) : types_scope.

Section mailbox_types_environment.

Context `{M : IMessage Message}.

(** Type environments are list of usage-annotated types because
    de Bruijn indices are used to represent variables.
*)
(* TODO: Maybe move to own section or file *)
Definition Env := list TUsage.

Inductive Member : TUsage -> Env -> Prop :=
    Z : forall env t, Member t (cons t env)
  | S : forall env t s, Member t env -> Member t (cons s env).

(*
Fixpoint lookup {env : Environment} {n : nat} (p : n < length env) : TUsage.
Proof.
  induction n.
  - destruct env eqn:E.
    + simpl in *; now apply PeanoNat.Nat.nlt_0_r in p.
    + simpl in *. apply t.
  - destruct env eqn:E.
    + simpl in *; now apply PeanoNat.Nat.nlt_0_r in p.
    + simpl in *. apply IHn. lia.
Defined.

Fixpoint count {env : Environment} {n : nat} (p : n < length env) : Member (lookup p) env.
Proof.
  induction n; destruct env eqn:E; simpl in *.
  - inversion p.
  - apply Z.
  - inversion p.
  - apply IHn.
Qed.
*)
(** Definition 3.4 of environment subtyping.
    For now we ignore the premise about variables not being in the domain
*)
Inductive EnvironmentSubtype : Env -> Env -> Prop :=
    EnvSubtypeEmpty : EnvironmentSubtype nil nil
  | EnvSubtypeUn : forall T env1 env2, Unrestricted T -> EnvironmentSubtype env1 env2 -> EnvironmentSubtype (cons T env1) env2
  | EnvSubtypeSub : forall T1 T2 env1 env2, Subtype T1 T2 -> EnvironmentSubtype env1 env2 -> EnvironmentSubtype (cons T2 env1) (cons T2 env2).

(** Definition 3.8 of environment combination.
    For now we ignore the premise about variables not being in the domain
*)
Inductive EnvironmentCombination : Env -> Env -> Env -> Prop :=
    EnvCombEmpty : EnvironmentCombination nil nil nil
  | EnvCombLeft : forall T env1 env2 env, EnvironmentCombination env1 env2 env -> EnvironmentCombination (cons T env1) env2 (cons T env)
  | EnvCombRight : forall T env1 env2 env, EnvironmentCombination env1 env2 env -> EnvironmentCombination env1 (cons T env2) (cons T env)
  | EnvCombBoth : forall T T1 T2 env1 env2 env, EnvironmentCombination env1 env2 env -> T1 ▷ T2 ~= T -> EnvironmentCombination (cons T1 env1) (cons T2 env2) (cons T env).

(** Definition 3.9 of disjoint environment combination.
    For now we ignore the premise about variables not being in the domain
*)
Inductive EnvironmentDisjointCombination : Env -> Env -> Env -> Prop :=
    EnvDisCombEmpty : EnvironmentDisjointCombination nil nil nil
  | EnvDisCombLeft : forall T env1 env2 env, EnvironmentDisjointCombination env1 env2 env -> EnvironmentDisjointCombination (cons T env1) env2 (cons T env)
  | EnvDisCombRight : forall T env1 env2 env, EnvironmentDisjointCombination env1 env2 env -> EnvironmentDisjointCombination env1 (cons T env2) (cons T env)
  | EnvDisCombBoth : forall T env1 env2 env, EnvironmentDisjointCombination env1 env2 env -> EnvironmentDisjointCombination (cons T env1) (cons T env2) (cons T env).

(** 
  Definition of splitting an environment into n environments.
  A list is used to keep track of the environments
*)
Inductive EnvironmentDisjointCombinationN : list Env -> Env -> Prop :=
    EnvDisComb2 : forall env env1 env2,
      EnvironmentDisjointCombination env1 env2 env ->
      EnvironmentDisjointCombinationN [env1 ; env2] env
  | EnvDisCombN : forall env env1 env2 env3 envList,
      EnvironmentDisjointCombination env1 env2 env3 ->
      EnvironmentDisjointCombinationN (env3 :: envList) env ->
      EnvironmentDisjointCombinationN (env1 :: env2 :: envList) env.

Fixpoint returnEnvironment (env : Env) : Env := map returnUsage env.
Fixpoint secondEnvironment (env : Env) : Env := map secondUsage env.

(** An environment is Base if it only contains base types *)
Fixpoint BaseEnv (e : Env) : Prop :=
  match e with
  | nil => True
  | (TUBase _ :: env') => BaseEnv env'
  | _ => False
  end.

End mailbox_types_environment.

Notation "Env1 ≤ₑ Env2" := (EnvironmentSubtype Env1 Env2) (at level 80) : types_scope.
Notation "Env1 ▷ₑ Env2 ~= Env" := (EnvironmentCombination Env1 Env2 Env) (at level 80) : types_scope.
Notation "Env1 +ₑ Env2 ~= Env" := (EnvironmentDisjointCombination Env1 Env2 Env) (at level 80) : types_scope.
Notation "[ Env1 ]+ₑ ~= Env" := (EnvironmentDisjointCombinationN Env1 Env) (at level 80) : types_scope.
Notation "⌊ Env ⌋ₑ" := (returnEnvironment Env) : types_scope.
Notation "⌈ Env ⌉ₑ" := (secondEnvironment Env) : types_scope.
