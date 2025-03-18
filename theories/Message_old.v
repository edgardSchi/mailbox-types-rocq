Section Message_def.

(** A message is a type with decidable equality *)
Class IMessage Message : Type :=
  {
    message_eq: Message -> Message -> Prop;
    message_eq_equiv : Equivalence message_eq;
    message_eq_dec : forall m n, {message_eq m n} + {~ message_eq m n};
  }.

End Message_def.

Section MessageConfig_def.

Generalizable All Variables.

Context `{IM : IMessage Message}.

(** A mailbox configuration is a multiset of messages *)
Definition MailboxConfig := multiset Message.

Definition EmptyMailbox := EmptyBag Message.
Definition SingletonMailbox (m : Message) := SingletonBag message_eq message_eq_dec m.

Definition mailbox_union (m1 m2 : MailboxConfig) := munion m1 m2.
Definition mailbox_eq (m1 m2 : MailboxConfig) := meq m1 m2.

Global Instance mailbox_eq_Equiv : Equivalence mailbox_eq.
Proof.
  constructor.
  - unfold Reflexive; apply meq_refl.
  - unfold Symmetric; apply meq_sym.
  - unfold Transitive; apply meq_trans.
Defined.

Lemma mailbox_union_comm : forall m1 m2, mailbox_eq (mailbox_union m1 m2) (mailbox_union m2 m1).
Proof.
  unfold mailbox_union; unfold mailbox_eq; apply munion_comm.
Qed.

Lemma mailbox_union_empty_right : forall m, mailbox_eq m (mailbox_union m EmptyMailbox).
Proof.
  unfold mailbox_union.
  unfold mailbox_eq.
  unfold EmptyMailbox.
  apply munion_empty_right.
Qed.

Lemma mailbox_union_empty_left : forall m, mailbox_eq m (mailbox_union EmptyMailbox m).
Proof.
  unfold mailbox_union.
  unfold mailbox_eq.
  unfold EmptyMailbox.
  apply munion_empty_left.
Qed.

Global Instance mailbox_eq_Proper : Proper (mailbox_eq ==> mailbox_eq ==> mailbox_eq) mailbox_union.
Proof.
  intros a b Eq1 c d Eq2.
  unfold mailbox_eq in *.
  unfold mailbox_union in *.
  unfold meq in *.
  unfold munion in *.
  simpl.
  intros m.
  rewrite (Eq1 m).
  rewrite (Eq2 m).
  auto.
Defined.

Lemma mailbox_empty_EmptyMailbox : forall m, mailbox_eq m EmptyMailbox -> m = EmptyMailbox.
Proof.
  intros m mEq.
  unfold mailbox_eq in mEq.
  unfold meq in mEq.
  unfold multiplicity in mEq.
  simpl in *.
  unfold EmptyMailbox.
  unfold EmptyBag.
  destruct m.
  simpl in *.
  f_equal.

  rewrite mEq.

  
End MessageConfig_def.

Declare Scope mailbox_config_scope.

Infix "=ᵐᵇ" := mailbox_eq (at level 71, left associativity) : mailbox_config_scope.
Infix "⊎" := mailbox_union (at level 68, left associativity) : mailbox_config_scope.
Notation "⟨ M ⟩" := (SingletonMailbox M).
Notation "⟨⟩" := (EmptyMailbox).

Open Scope mailbox_config_scope.

(** ** Strings as messages *)
Require Import String.
Section StringMessages.

Global Instance StringMessage : IMessage string :=
{
  message_eq_dec := string_dec
}.

End StringMessages.

(** ** Example finite message set *)
Section SendReceiveMessages.

Inductive SendReceive : Type :=
    Send : SendReceive
  | Receive : SendReceive.

Definition SendReceive_eq (m1 m2 : SendReceive) : Prop :=
  match m1, m2 with
  | Send, Send => True
  | Receive, Receive => True
  | _, _ => False
  end.

Instance SendReceive_eq_equiv : Equivalence SendReceive_eq.
Proof.
  constructor.
  - unfold Reflexive; intros x; destruct x; now simpl.
  - unfold Symmetric; intros x y Eq. destruct x; destruct y; simpl; simpl in Eq; auto.
  - unfold Transitive; intros x y Eq1 Eq2; destruct x;
    destruct y; destruct Eq1; destruct Eq2; auto.
Qed.

Lemma SendReceive_eq_dec : forall m n, {SendReceive_eq m n} + {~ SendReceive_eq m n}.
Proof.
  intros m n; destruct m; destruct n; simpl; auto.
Defined.

Global Instance SendReceiveMessage : IMessage SendReceive :=
{
  message_eq := SendReceive_eq;
  message_eq_dec := SendReceive_eq_dec
}.

End SendReceiveMessages.
