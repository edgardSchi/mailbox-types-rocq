(** * Definition of messages *)

Require Import Setoid.
Require Import Sets.Multiset.
Require Import Classes.Morphisms.
Require Import List.
Require Import Permutation.

Generalizable All Variables.

Section Message_def.

(** A message is a type with decidable Leibniz equality *)
Class IMessage Message : Type :=
  {
    eq_dec : forall m n, {@eq Message m n} + {~ @eq Message m n}
  }.

End Message_def.

Section MessageConfig_def.

Context `{IM : IMessage Message}.

Definition MailboxConfig := list Message.
Definition EmptyMailbox : MailboxConfig := nil.
Definition SingletonMailbox (m : Message) : MailboxConfig := m :: nil.

Definition mailbox_eq (m1 m2 : MailboxConfig) : Prop := Permutation m1 m2.
Definition mailbox_union (m1 m2 : MailboxConfig) : MailboxConfig := app m1 m2.

End MessageConfig_def.

Section MessageConfig_props.

Context `{IM : IMessage Message}.
Implicit Types m : @MailboxConfig Message.

Lemma mailbox_union_comm : forall m1 m2, mailbox_eq (mailbox_union m1 m2) (mailbox_union m2 m1).
Proof.
  intros.
  unfold mailbox_union.
  unfold mailbox_eq.
  apply Permutation_app_comm.
Qed.

Lemma mailbox_union_empty_right : forall m, mailbox_eq m (mailbox_union m EmptyMailbox).
Proof.
  intros.
  unfold mailbox_union.
  unfold mailbox_eq.
  unfold EmptyMailbox.
  now rewrite app_nil_r.
Qed.

Lemma mailbox_union_empty_left : forall m, mailbox_eq m (mailbox_union EmptyMailbox m).
Proof.
  intros.
  unfold mailbox_union.
  unfold mailbox_eq.
  unfold EmptyMailbox.
  now rewrite app_nil_l.
Qed.

Lemma mailbox_union_assoc : forall m n o,
  mailbox_eq (mailbox_union m (mailbox_union n o)) (mailbox_union (mailbox_union m n) o).
Proof.
  unfold mailbox_eq.
  unfold mailbox_union.
  intros.
  now rewrite <- app_assoc.
Qed.

Lemma SingletonMailbox_eq : forall e m, mailbox_eq (SingletonMailbox e) m -> m = SingletonMailbox e.
Proof.
  intros e m mbEq.
  unfold SingletonMailbox in *.
  unfold mailbox_eq in *.
  generalize (Permutation_length mbEq).
  simpl.
  intros l.
  induction m.
  - easy.
  - simpl in *. inversion l.
    generalize (length_zero_iff_nil m).
    intros mNil.
    destruct mNil as [lM mNil].
    symmetry in H0.
    apply lM in H0.
    subst.
    apply Permutation_length_1 in mbEq. now subst.
Qed.

Global Instance mailbox_eq_Proper : Proper (@mailbox_eq Message ==> @mailbox_eq Message ==> @mailbox_eq Message) mailbox_union.
Proof.
  intros a b Eq1 c d Eq2.
  unfold mailbox_eq in *.
  unfold mailbox_union in *.
  now apply Permutation_app.
Defined.

End MessageConfig_props.

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
  eq_dec := string_dec
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

Lemma SendReceive_eq_dec : forall m n : SendReceive, {m = n} + {m <> n}.
Proof.
  intros m n; destruct m; destruct n;
  try (auto);
  right; unfold not; intros; discriminate H.
Defined.

Instance SendReceiveMessage : IMessage SendReceive :=
{
  eq_dec := SendReceive_eq_dec
}.

End SendReceiveMessages.

