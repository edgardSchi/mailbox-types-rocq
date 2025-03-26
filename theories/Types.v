(** * Syntax of types *)

From MailboxTypes Require Import Message.
From MailboxTypes Require Import MailboxPatterns.

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

(* TODO: Define return and second for type environments *)

Inductive UsageSubtype : UsageAnnotation -> UsageAnnotation -> Prop :=
    usageSubtype_refl : forall n, UsageSubtype n n
  | usageSubtype_le   : UsageSubtype Returnable SecondClass.

Inductive Subtype : TUsage -> TUsage -> Prop :=
    subtype_base : forall c, Subtype (TUBase c) (TUBase c)
  | subtype_input : forall e f n1 n2,
      MPInclusion e f -> UsageSubtype n1 n2 -> Subtype (TUUsage n1 (MTInput e)) (TUUsage n2 (MTInput f))
  | subtype_output : forall e f n1 n2,
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
Notation "T ◦" := (TUUsage SecondClass T) (at level 75): types_scope.
Notation "•" := (Returnable) : types_scope.
Notation "T •" := (TUUsage Returnable T) (at level 75): types_scope.
Notation "⌊ T ⌋" := (returnType T) : types_scope.
Notation "⌊ T ⌋ⁿ" := (returnUsage T) : types_scope.
Notation "⌈ T ⌉" := (secondType T) : types_scope.
Notation "⌈ T ⌉ⁿ" := (secondUsage T) : types_scope.
Notation "n1 ≤ⁿ n2" := (UsageSubtype n1 n2) (at level 80) : types_scope.
Notation "A ≤ B" := (Subtype A B) (at level 80) : types_scope.
Notation "A ≃ B" := (TypeEqual A B) (at level 80) : types_scope.

Section mailbox_types_classes.

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
