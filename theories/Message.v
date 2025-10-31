(** * Definition of messages *)

From Stdlib Require Import Setoid.
From Stdlib Require Import Sets.Multiset.
From Stdlib Require Import Classes.Morphisms.
From Stdlib Require Import List.
From Stdlib Require Import Permutation.

Generalizable All Variables.

Section Message_def.

  (** A message is a type with decidable Leibniz equality
      as well as the number of values it contains.
  *)
  Class IMessage Message : Type :=
    {
      eq_dec : forall m n : Message, {m = n} + {m <> n}
    ; content_size : Message -> nat
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

Declare Scope mailbox_config_scope.

Infix "=ᵐᵇ" := mailbox_eq (at level 71, left associativity) : mailbox_config_scope.
Infix "⊎" := mailbox_union (at level 68, left associativity) : mailbox_config_scope.
Notation "⟨ M ⟩" := (SingletonMailbox M).
Notation "⟨⟩" := (EmptyMailbox).

Open Scope mailbox_config_scope.

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

  Lemma mailbox_union_empty : forall m1 m2,
    mailbox_eq EmptyMailbox (mailbox_union m1 m2) -> m1 = EmptyMailbox /\ m2 = EmptyMailbox .
  Proof.
    intros * Eq; apply Permutation_nil in Eq; now apply app_eq_nil.
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

  (** If a mailbox contains message [m] and is equal to the union of
      two other mailboxes [a] and [b], then [m] can moved in front.
  *)
  Lemma mailbox_eq_move_from_middle : forall (m : Message) mc a b,
    (⟨ m ⟩ ⊎ mc) =ᵐᵇ (a ⊎ b) ->
    exists a' b', (⟨ m ⟩ ⊎ mc) =ᵐᵇ (⟨ m ⟩ ⊎ a' ⊎ b').
  Proof.
    intros * Perm.
    assert (mIn : In m (a ++ b)).
    {
      apply Permutation_in with (l := m :: mc).
      easy.
      now constructor.
    }
    apply in_split in mIn.
    destruct mIn as [l1 [l2 Split]].
    exists l1, l2.
    simpl.
    rewrite Permutation_middle.
    now rewrite <- Split.
  Qed.

  (** If a mailbox contains message [m] and is equal to the union of
      two other mailboxes [a] and [b], then [m] must be in either in
      [a] or [b].
  *)
  Lemma mailbox_eq_union_split : forall (m : Message) mc a b,
    (⟨ m ⟩ ⊎ mc) =ᵐᵇ (a ⊎ b) ->
    (exists a', (⟨ m ⟩ ⊎ mc) =ᵐᵇ (⟨ m ⟩ ⊎ a' ⊎ b)) \/
    (exists b', (⟨ m ⟩ ⊎ mc) =ᵐᵇ (⟨ m ⟩ ⊎ a ⊎ b')).
  Proof.
    intros * Eq.
    assert (mIn : In m (a ⊎ b)).
    {
      eapply Permutation_in with (l := ⟨ m ⟩ ⊎ mc).
      now symmetry.
      now constructor.
    }
    apply in_app_or in mIn.
    destruct mIn as [InA | InB].
    - left.
      apply in_split in InA.
      destruct InA as [l1 [l2 Split]].
      subst.
      rewrite <- Permutation_middle in Eq.
      now exists (l1 ++ l2).
    - right.
      apply in_split in InB.
      destruct InB as [l1 [l2 Split]].
      subst.
      rewrite <- Permutation_middle in Eq.
      rewrite <- Permutation_middle in Eq.
      now exists (l1 ++ l2).
  Qed.

End MessageConfig_props.

(** ** Strings as messages *)
From Stdlib Require Import String.
Section StringMessages.

  Global Instance StringMessage : IMessage string :=
  {
    eq_dec := string_dec
    (* Each string contains exactly one value *)
  ; content_size := fun _ => 1
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
  ; content_size := fun _ => 1
  }.

End SendReceiveMessages.

