(** * Type syntax of mailbox types *)

From MailboxTypes Require Import Message.
Open Scope mailbox_config_scope.

Generalizable All Variables.

Section MPattern_defs.

Context `{MessageInterface : IMessage Message}.

(**
  Mailbox pattern definition.
  A mailbox pattern is accompanied by the message type
  [Message], i.e. what kind of messages are inside the mailbox.
*)
Inductive MPattern `{IMessage Message} : Type :=
    MPZero : MPattern
  | MPOne : MPattern
  | MPMessage : Message -> MPattern
  | MPChoice : MPattern -> MPattern -> MPattern
  | MPComp : MPattern -> MPattern -> MPattern
  | MPStar : MPattern -> MPattern.

(** Repeated choice a mailbox pattern *)
Fixpoint Pow (p : MPattern) (n : nat) : MPattern :=
  match n with
  | 0 => MPOne
  | S n => MPChoice p (Pow p n)
  end.

(**
   The semantics of mailbox patterns are defined by a relation
   between a mailbox config and a pattern.
*)
Inductive valueOf : MailboxConfig -> MPattern -> Prop :=
    MPValueOne : valueOf EmptyMailbox MPOne
  | MPValueMessage : forall m, valueOf (SingletonMailbox m) (MPMessage m)
  | MPValueChoiceLeft : forall p1 p2 m, valueOf m p1 -> valueOf m (MPChoice p1 p2)
  | MPValueChoiceRight : forall p1 p2 m, valueOf m p2 -> valueOf m (MPChoice p1 p2)
  | MPValueComp : forall p1 p2 m a b, valueOf a p1 -> valueOf b p2 -> m =ᵐᵇ (a ⊎ b) -> valueOf m (MPComp p1 p2)
  | MPValueStar : forall p m, (exists n, valueOf m (Pow p n)) -> valueOf m (MPStar p).

Definition MPInclusion (e f : MPattern) : Prop :=
  forall m, valueOf m e -> valueOf m f.

Definition MPEqual (e f : MPattern) : Prop :=
  MPInclusion e f /\ MPInclusion f e.

Lemma MPZero_empty : forall m, ~ (valueOf m MPZero).
Proof.
  intros m.
  destruct m.
  unfold not; intros valueOf; inversion valueOf.
Qed.
End MPattern_defs.

(** Notation on mailbox pattern. Basically the same as in the paper. *)
Declare Scope mailbox_pattern_scope.
Open Scope mailbox_pattern_scope.

Notation "𝟘" := MPZero : mailbox_pattern_scope.
Notation "𝟙" := MPOne : mailbox_pattern_scope.
Infix "⊕" := MPChoice (at level 66, left associativity) : mailbox_pattern_scope.
Infix "⊙" := MPComp (at level 65, left associativity) : mailbox_pattern_scope.
Notation "⋆ E" := (MPStar E) (at level 64) : mailbox_pattern_scope.
Notation "« M »" := (MPMessage M) : mailbox_pattern_scope.
Infix "∈" := valueOf (at level 67, left associativity) : mailbox_pattern_scope.

Require Import String.
Open Scope string_scope.

Lemma Test : ⟨⟩ ∈ (𝟙 ⊕ 𝟘).
Proof.
  apply MPValueChoiceLeft.
  apply MPValueOne.
Qed.

Lemma Test1 : (⟨ "m" ⟩ ⊎ ⟨ "n" ⟩) ∈ (« "n" » ⊙ « "m" »).
Proof.
  eapply MPValueComp.
  - apply MPValueMessage.
  - apply MPValueMessage.
  - now rewrite mailbox_union_comm.
Qed.

(* TODO
Lemma Test2 : MPEqual (𝟙 ⊕ 𝟘 ⊕ (« "m" » ⊙ « "n" »)) (𝟙 ⊕ (« "n" » ⊙ « "m" »)).
Proof.
  unfold MPEqual.
  split.
  - unfold MPInclusion.
    intros m E.
*)

Section mailbox_type_def.

Context `{M : IMessage Message}.

(** Mailbox type definition *)
Inductive MType `{IMessage Message} : Type :=
    MTOutput : MPattern -> MType
  | MTInput  : MPattern -> MType.

End mailbox_type_def.
