(** * Syntax of types *)

Require Import Lia.

From MailboxTypes Require Export Message.
From MailboxTypes Require Export MailboxPatterns.

Require Import List.
Import ListNotations.

Generalizable All Variables.

Section type_def.

Context `{M : IMessage Message}.

(** Mailbox type definition *)
Inductive MType (*`{IMessage Message}*) : Type :=
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


(** A cruft type is either a base type or irrelevant.
    A cruft type represents a type that can be added
   through the subtyping rule which may not be used
   by a term.
*)
Definition TTCruft (t : TType) : Prop :=
  match t with
  | TTBase _ => True
  | TTMailbox m => Irrelevant m
  end.

(** A cruft usage-type is either a base type or the usage is
    secondClass and the type is cruft
*)
Definition TUCruft (t : TUsage) : Prop :=
  match t with
  | TUBase _ => True
  | TUUsage SecondClass ty => TTCruft (TTMailbox ty)
  | _ => False
  end.


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
Notation "J ▷ K ~= L" := (TypeUsageCombination J K L) (at level 80) : types_scope.
