(** * Typing environments *)

From MailboxTypes Require Export Types.
From MailboxTypes Require Import Util.

Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

(** ** Definition of environments and operations on them *)
Section environment_def.

Context `{M : IMessage Message}.

(** A type environment is represented as a list of option types.
    For example the environment [[None, Some Int, Some Bool, None]]
    represents
    0 |-> None
    1 |-> Int
    2 |-> Bool
    3 |-> None

   This represented is chosen to keep avoid shifting de Bruijn indices
   when splitting an environment.
*)
Definition Env := list (option TUsage).

(** Lookup the type of an variable in an environment *)
Fixpoint lookup (n : nat) (env : Env) : option TUsage :=
  match n, env with
  | _, nil => None
  | 0, (None :: env') => None
  | 0, (Some T :: env') => Some T
  | S n', (_ :: env') => lookup n' env'
  end.

(** Convert a list of types to an environment. This reverses the list. *)
Definition toEnv (l : list TUsage) : Env :=
  map Some (rev l).

(** Definition 3.4 of environment subtyping.
    Subtyping of environments includes weakening for unrestricted types.
    This representation relates two environments of equal length, but
    they may contain different amounts of types
*)
Inductive EnvironmentSubtype : Env -> Env -> Prop :=
    EnvSubtypeEmpty : EnvironmentSubtype nil nil
  | EnvSubtypeNone : forall env1 env2,
      EnvironmentSubtype env1 env2 ->
      EnvironmentSubtype (None :: env1) (None :: env2)
  | EnvSubtypeUn : forall env1 env2 T,
      Unrestricted T ->
      EnvironmentSubtype env1 env2 ->
      EnvironmentSubtype (Some T :: env1) (None :: env2)
  | EnvSubtypeSub : forall env1 env2 T1 T2,
      Subtype T1 T2 ->
      EnvironmentSubtype env1 env2 ->
      EnvironmentSubtype (Some T1 :: env1) (Some T2 :: env2).

(** Strict environment subtyping.
    Strict subtyping of environments is same as normal
    subtyping but the domains of both environments must be
    equal. In our representation this means that for every
    index in every list, both contain either None or Some.
*)
Inductive EnvironmentSubtypeStrict : Env -> Env -> Prop :=
    EnvSubtypeStrEmpty : EnvironmentSubtypeStrict nil nil
  | EnvSubtypeStrNone : forall env1 env2,
      EnvironmentSubtypeStrict env1 env2 ->
      EnvironmentSubtypeStrict (None :: env1) (None :: env2)
  | EnvSubtypeStrSub : forall env1 env2 T1 T2,
      Subtype T1 T2 ->
      EnvironmentSubtypeStrict env1 env2 ->
      EnvironmentSubtypeStrict (Some T1 :: env1) (Some T2 :: env2).


(** Definition 3.8 of environment combination.
    This representation relates three environments of equal length, but
    they may contain different amounts of types
*)
Inductive EnvironmentCombination : Env -> Env -> Env -> Prop :=
    EnvCombEmpty : EnvironmentCombination nil nil nil
  (* Special constructor for our representation of environments *)
  (* TODO: Check if this is correct *)
  | EnvCombNone : forall env1 env2 env,
      EnvironmentCombination env1 env2 env ->
      EnvironmentCombination (None :: env1) (None :: env2) (None :: env)
  | EnvCombLeft : forall env1 env2 env T,
      EnvironmentCombination env1 env2 env ->
      EnvironmentCombination (Some T :: env1) (None :: env2) (Some T :: env)
  | EnvCombRight : forall env1 env2 env T,
      EnvironmentCombination env1 env2 env ->
      EnvironmentCombination (None :: env1) (Some T :: env2) (Some T :: env)
  | EnvCombBoth : forall T env1 env2 env T1 T2,
      EnvironmentCombination env1 env2 env ->
      T1 ▷ T2 ~= T ->
      EnvironmentCombination (Some T1 :: env1) (Some T2 :: env2) (Some T :: env).

(** Definition 3.9 of disjoint environment combination.
    This representation relates three environments of equal length, but
    they may contain different amounts of types
*)
Inductive EnvironmentDisjointCombination : Env -> Env -> Env -> Prop :=
    EnvDisCombEmpty : EnvironmentDisjointCombination nil nil nil
  (* Special constructor for our representation of environments *)
  (* TODO: Check if this is correct *)
  | EnvDisCombNone : forall env1 env2 env,
      EnvironmentDisjointCombination env1 env2 env ->
      EnvironmentDisjointCombination (None :: env1) (None :: env2) (None :: env)
  | EnvDisCombLeft : forall env1 env2 env T,
      EnvironmentDisjointCombination env1 env2 env ->
      EnvironmentDisjointCombination (Some T :: env1) (None :: env2) (Some T :: env)
  | EnvDisCombRight : forall env1 env2 env T,
      EnvironmentDisjointCombination env1 env2 env ->
      EnvironmentDisjointCombination (None :: env1) (Some T :: env2) (Some T :: env)
  | EnvDisCombBoth : forall env1 env2 env BT,
      EnvironmentDisjointCombination env1 env2 env ->
      EnvironmentDisjointCombination
        (Some (TUBase BT) :: env1) (Some (TUBase BT) :: env2) (Some (TUBase BT) :: env).

Inductive EnvironmentDisjointCombinationN : list Env -> Env -> Prop :=
  | EnvDisComb1 : forall env,
      EnvironmentDisjointCombinationN [env] env
  | EnvDisComb2 : forall env env1 env2,
      EnvironmentDisjointCombination env1 env2 env ->
      EnvironmentDisjointCombinationN [env1 ; env2] env
  | EnvDisCombN : forall env env1 env2 env3 envList,
      EnvironmentDisjointCombination env1 env2 env3 ->
      EnvironmentDisjointCombinationN (env3 :: envList) env ->
      EnvironmentDisjointCombinationN (env1 :: env2 :: envList) env.

Definition returnEnvironment (env : Env) : Env := map_maybe returnUsage env.
Definition secondEnvironment (env : Env) : Env := map_maybe secondUsage env.

(** An environment is Base if it only contains base types *)
Fixpoint BaseEnv (e : Env) : Prop :=
  match e with
  | nil => True
  | (Some (TUBase _) :: env') => BaseEnv env'
  | (None :: env') => BaseEnv env'
  | _ => False
  end.

Definition CruftEnv : Env -> Prop :=
  ForallMaybe TUCruft.


(** An empty environment contains only None as entries *)
Definition EmptyEnv (e : Env) : Prop := Forall (fun x => x = None) e.

(** A singleton environment contains only a single type *)
Fixpoint SingletonEnv (e : Env) : Prop :=
  match e with
  | nil => False
  | None :: e' => SingletonEnv e'
  | (Some _) :: e' => EmptyEnv e'
  end.

End environment_def.

(** Notation for environments *)
Declare Scope environment_scope.
Open Scope environment_scope.

Notation "Env1 ≤ₑ Env2" := (EnvironmentSubtype Env1 Env2) (at level 80) : environment_scope.
Notation "Env1 ≼ₑ Env2" := (EnvironmentSubtypeStrict Env1 Env2) (at level 80) : environment_scope.
Notation "Env1 ▷ₑ Env2 ~= Env" := (EnvironmentCombination Env1 Env2 Env) (at level 80) : environment_scope.
Notation "Env1 +ₑ Env2 ~= Env" := (EnvironmentDisjointCombination Env1 Env2 Env) (at level 80) : environment_scope.
(* TODO: Change the below notation. It sometimes collides with list notations *)
Notation "[ Env1 ]+ₑ ~= Env" := (EnvironmentDisjointCombinationN Env1 Env) (at level 80) : environment_scope.
Notation "⌊ Env ⌋ₑ" := (returnEnvironment Env) : environment_scope.
Notation "⌈ Env ⌉ₑ" := (secondEnvironment Env) : environment_scope.

Section environment_properties.

Context `{M : IMessage Message}.

End environment_properties.
