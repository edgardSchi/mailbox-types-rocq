(** * Type syntax of mailbox types *)

Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.

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
  | S n => MPComp p (Pow p n)
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
  intros m. destruct m;
  unfold not; intros valueOf; inversion valueOf.
Qed.

Lemma MPOne_EmptyMailbox : forall m, valueOf m MPOne -> m =ᵐᵇ EmptyMailbox.
Proof.
  intros m mIn. now inversion mIn.
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
Infix "≈" := MPEqual (at level 71, left associativity) : mailbox_pattern_scope.

Section MPattern_props.

Context `{MessageInterface : IMessage Message}.

Example Example1 : ⟨⟩ ∈ (𝟙 ⊕ 𝟘).
Proof.
  apply MPValueChoiceLeft.
  apply MPValueOne.
Qed.

Lemma MPInclusion_trans : forall e f g, MPInclusion e f -> MPInclusion f g -> MPInclusion e g.
Proof.
  intros e f g Inc1 Inc2.
  unfold MPInclusion in *.
  intuition.
Qed.

Lemma MPEqual_refl : forall e, e ≈ e.
Proof.
  intros.
  unfold MPEqual.
  split; unfold MPInclusion; easy.
Qed.

Lemma MPEqual_sym : forall e f, e ≈ f -> f ≈ e.
Proof.
  intros e f Eq.
  unfold MPEqual in *.
  intuition.
Qed.

Lemma MPEqual_trans : forall e f g, e ≈ f -> f ≈ g -> e ≈ g.
Proof.
  intros e f g Eq1 Eq2.
  unfold MPEqual in *.
  destruct Eq1 as [Eq1 Eq1'].
  destruct Eq2 as [Eq2 Eq2'].
  split; eapply MPInclusion_trans.
  apply Eq1. apply Eq2.
  apply Eq2'. apply Eq1'.
Qed.

Global Instance MPEqual_equiv : Equivalence MPEqual.
Proof.
  constructor.
  - unfold Reflexive. apply MPEqual_refl.
  - unfold Symmetric. apply MPEqual_sym.
  - unfold Transitive. apply MPEqual_trans.
Defined.

Global Instance MPEqual_valueOf_Proper : Proper (eq ==> MPEqual ==> iff) valueOf.
Proof.
  intros m1 m2 mbEq mp1 mp2 mpEq.
  subst.
  split.
  - intros mIn.
    induction mIn; inversion mpEq as [Eq1 Eq2]; unfold MPInclusion in *; apply Eq1;
    try (now constructor).
    eapply MPValueComp. apply mIn1. apply mIn2. apply H.
  - intros mIn.
    induction mIn; inversion mpEq as [Eq1 Eq2]; unfold MPInclusion in *; apply Eq2;
    try (now constructor).
    eapply MPValueComp. apply mIn1. apply mIn2. apply H.
Defined.

Lemma mailbox_eq_valueOf : forall m1 m2 mp, m1 =ᵐᵇ m2 -> m1 ∈ mp -> m2 ∈ mp.
Proof.
  intros ? ? ? mbEq mIn.
  induction mIn as [| | | | ? ? ? ? ? ? ? ? ? mbEq2 | ? ? pow].
  (* TODO use lemma for empty mailbox *)
  - unfold mailbox_eq in *;
    apply Permutation.Permutation_nil in mbEq; subst; constructor.
  - apply SingletonMailbox_eq in mbEq; subst; constructor.
  - constructor; now apply IHmIn.
  - apply MPValueChoiceRight; now apply IHmIn.
  - eapply MPValueComp; try (apply mIn1 || apply mIn2).
    etransitivity. symmetry. apply mbEq. apply mbEq2.
  - constructor; destruct pow as [n mIn2]; exists n;
    induction n; simpl in *;
    inversion mIn2 as [| | | | ? ? ? ? ? mInA mInB mbEq2 |]; subst.
    + (* TODO use lemma for empty mailbox *)
      apply Permutation.Permutation_nil in mbEq. subst. constructor.
    + eapply MPValueComp. apply mInA. apply mInB.
      etransitivity. symmetry. apply mbEq. apply mbEq2.
Qed.

Global Instance mailbox_eq_valueOf_Proper : Proper (mailbox_eq ==> MPEqual ==> iff) valueOf.
Proof.
  intros m1 m2 mbEq mp1 mp2 mpEq.
  split.
  - intros mIn.
    eapply mailbox_eq_valueOf.
    apply mbEq.
    now setoid_rewrite <- mpEq.
  - intros.
    eapply mailbox_eq_valueOf.
    symmetry.
    apply mbEq.
    now setoid_rewrite mpEq.
Qed.

Lemma MPChoice_unit : forall e, e ⊕ 𝟘 ≈ e.
Proof.
  intros e.
  unfold MPEqual; split; unfold MPInclusion; intros m mIn.
  - now inversion mIn.
  - now constructor.
Qed.

Lemma MPComp_unit : forall e, e ⊙ 𝟙 ≈ e.
Proof.
  intros e.
  unfold MPEqual; split; unfold MPInclusion; intros m mIn.
  - inversion mIn; subst. apply MPOne_EmptyMailbox in H3.
    setoid_rewrite H3 in H4.
    rewrite mailbox_union_comm in H4.
    rewrite <- mailbox_union_empty_left in H4.
    now setoid_rewrite H4.
  - inversion mIn; subst;
    try (apply MPValueComp with (a := nil) (b := nil); constructor; constructor);
    try (apply MPValueComp with (a := ⟨ m0 ⟩) (b := nil);
        constructor; constructor; reflexivity);
    try ( apply MPValueComp with (a := m) (b := nil);
        try (apply mIn || constructor);
             unfold mailbox_union; now rewrite List.app_nil_r
    ).
Qed.

(* TODO *)
(*
Lemma MPComp_assoc : forall e f g, e ⊙ (f ⊙ g) ≈ (e ⊙ f) ⊙ g.
Proof.
  intros e f g.
  unfold MPEqual.
  split.
  - unfold MPInclusion.
    intros m mIn.
    destruct e; destruct f; destruct g.
    + simpl.
*)

End MPattern_props.

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
