(** * Syntax and semantics of mailbox patterns *)

Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.
Require Import List.

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
Infix "⊑" := MPInclusion (at level 71, left associativity) : mailbox_pattern_scope.
Infix "≈" := MPEqual (at level 72, left associativity) : mailbox_pattern_scope.

Section MPattern_residuals.

Context `{MessageInterface : IMessage Message}.

(** Definition from Fig. 5 of mailbox pattern residiuals.
    Calculates the pattern after a message is consumed
*)
Inductive PatternResidual : MPattern -> MPattern -> MPattern -> Prop :=
    MPResZero : forall m, PatternResidual 𝟘 (« m ») 𝟘
  | MPResOne : forall m, PatternResidual 𝟙 (« m ») 𝟘
  | MPResMessageCorrect : forall m, PatternResidual (« m ») (« m ») 𝟙
  | MPResMessageWrong : forall m n, ~ (m = n) -> PatternResidual (« m ») (« n ») 𝟘
  | MPResChoice : forall e e' f f' m,
      PatternResidual e (« m ») e' ->
      PatternResidual f (« m ») f' ->
      PatternResidual (e ⊕ f) (« m ») (e' ⊕ f')
  | MPResComp : forall e e' f f' m,
      PatternResidual e (« m ») e' ->
      PatternResidual f (« m ») f' ->
      PatternResidual (e ⊙ f) (« m ») ((e' ⊙ f) ⊕ (e ⊙ f'))
  (* This rule is not included in the paper, but otherwise we can't
     use the ⋆-operator. TODO: I guess we can use subtyping when needed

     Also, this definition is included in the original paper from
     2018.
     TODO: Check if this rule breaks something
  *)
  | MPResStar : forall e m e',
      PatternResidual e (« m ») e' ->
      PatternResidual (⋆ e) (« m ») (e' ⊙ ⋆ e).

(** Definition from Fig. 5 of pattern normal form for literals *)
Inductive PNFLit : MPattern -> MPattern -> Prop :=
    PNFLitZero : forall e, PNFLit e 𝟘
  | PNFLitOne : forall e, PNFLit e 𝟙
  | PNFLitComp : forall e f m e',
      PatternResidual e (« m ») e' ->
      f ≈ e' ->
      PNFLit e ((« m ») ⊙ f)
  | PNFLitChoice : forall e f1 f2,
      PNFLit e f1 ->
      PNFLit e f2 ->
      PNFLit e (f1 ⊕ f2).

(** Definition from Fig. 5 of pattern normal form *)
Inductive PNF : MPattern -> MPattern -> Prop :=
  PNFCon : forall e f, PNFLit e f -> PNF e f.

End MPattern_residuals.

Notation "E ⊧ F" := (PNF E F) (at level 98) : mailbox_pattern_scope.
Notation "E // F ~= G" := (PatternResidual E F G) (at level 99) : mailbox_pattern_scope.

Section MPattern_props.

Context `{MessageInterface : IMessage Message}.

(** Properties of mailbox patterns showing that they are a commutative Klenee algebra. *)

Example Example1 : ⟨⟩ ∈ (𝟙 ⊕ 𝟘).
Proof.
  apply MPValueChoiceLeft.
  apply MPValueOne.
Qed.

Lemma MPInclusion_trans : forall e f g, e ⊑ f -> f ⊑ g -> e ⊑ g.
Proof.
  intros e f g Inc1 Inc2;
  unfold MPInclusion in *;
  intuition.
Qed.

Lemma MPInclusion_refl : forall e, e ⊑ e.
Proof.
  intro e; unfold MPInclusion in *; intuition.
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


(** Proper instances to allow setoid rewrites under different contexts *)

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

Global Instance MPEqual_Proper : Proper (MPEqual ==> MPEqual ==> iff) MPEqual.
Proof.
  intros e1 f1 Eq1 e2 f2 Eq2.
  split.
  - intros Eq3.
    rewrite <- Eq1.
    rewrite <- Eq2.
    apply Eq3.
  - intros Eq3.
    rewrite Eq1.
    rewrite Eq2.
    apply Eq3.
Qed.

Global Instance MPComp_Proper : Proper (MPEqual ==> MPEqual ==> MPEqual) MPComp.
Proof.
  intros e1 f1 Eq1 e2 f2 Eq2.
  unfold "≈".
  unfold "⊑".
  split; intros m mIn; inversion mIn; subst.
  - eapply MPValueComp with (a := a) (b := b).
    now rewrite <- Eq1.
    now rewrite <- Eq2.
    easy.
  - eapply MPValueComp with (a := a) (b := b).
    now rewrite Eq1.
    now rewrite Eq2.
    easy.
Defined.

Global Instance MPChoice_Proper : Proper (MPEqual ==> MPEqual ==> MPEqual) MPChoice.
Proof.
  intros e1 f1 Eq1 e2 f2 Eq2.
  unfold "≈".
  unfold "⊑".
  split; intros m mIn; inversion mIn; subst.
  - apply MPValueChoiceLeft.
    now rewrite <- Eq1.
  - apply MPValueChoiceRight.
    now rewrite <- Eq2.
  - apply MPValueChoiceLeft.
    now rewrite Eq1.
  - apply MPValueChoiceRight.
    now rewrite Eq2.
Defined.

Global Instance Pow_Proper : Proper (MPEqual ==> eq ==> MPEqual) Pow.
Proof.
  intros e f Eq x y EqN.
  subst.
  induction y.
  - simpl. reflexivity.
  - simpl.
    unfold "≈".
    unfold "⊑" in *.
    split; intros m mIn; inversion mIn; subst.
    + apply MPValueComp with (a := a) (b := b).
      now rewrite <- Eq.
      now rewrite <- IHy.
      easy.
    + apply MPValueComp with (a := a) (b := b).
      now rewrite Eq.
      now rewrite IHy.
      easy.
Defined.

Global Instance MPStar_Proper : Proper (MPEqual ==> MPEqual) MPStar.
Proof.
  intros e f Eq.
  unfold "≈".
  unfold "⊑".
  split; intros m mIn; inversion mIn; subst.
  - destruct H1. rewrite Eq in H.
    apply MPValueStar.
    now exists x.
  - destruct H1. rewrite <- Eq in H.
    apply MPValueStar.
    now exists x.
Defined.


Lemma MPChoice_unit : forall e, e ⊕ 𝟘 ≈ e.
Proof.
  intros e.
  unfold MPEqual; split; unfold MPInclusion; intros m mIn.
  - now inversion mIn.
  - now constructor.
Qed.

Lemma MPChoice_idem : forall e, e ⊕ e ≈ e.
Proof.
  intro e.
  unfold MPEqual.
  split.
  - unfold MPInclusion.
    intros m mIn.
    now inversion mIn.
  - unfold MPInclusion.
    intros m mIn.
    now constructor.
Qed.

Lemma MPChoice_comm : forall e f, e ⊕ f ≈ f ⊕ e.
Proof.
  intros e f.
  unfold MPEqual.
  split; unfold MPInclusion; intros m mIn;
  inversion mIn; subst;
  try (now apply MPValueChoiceLeft);
  try (now apply MPValueChoiceRight).
Qed.

Lemma MPChoice_assoc : forall e f g, e ⊕ (f ⊕ g) ≈ (e ⊕ f) ⊕ g.
Proof.
  intros e f g.
  unfold MPEqual.
  split; unfold MPInclusion; intros m mIn.
  - inversion mIn as [ | | e' f' m' mIn' | e' f' m' mIn' | | ];
    subst.
    + now repeat apply MPValueChoiceLeft.
    + inversion mIn' as [ | | e' f' m' mIn'' | e' f' m' mIn'' | | ];
      subst.
      * apply MPValueChoiceLeft; now apply MPValueChoiceRight.
      * now apply MPValueChoiceRight.
  - inversion mIn as [ | | e' f' m' mIn' | e' f' m' mIn' | | ];
    subst.
    + inversion mIn' as [ | | e' f' m' mIn'' | e' f' m' mIn'' | | ];
      subst.
      * now apply MPValueChoiceLeft.
      * apply MPValueChoiceRight; now apply MPValueChoiceLeft.
    + now repeat apply MPValueChoiceRight.
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

Lemma MPComp_zero_left : forall e, 𝟘 ⊙ e ≈ 𝟘.
Proof.
  intros e.
  unfold MPEqual.
  split.
  - unfold MPInclusion.
    intros m mIn.
    inversion mIn. subst. inversion H1.
  - unfold MPInclusion.
    intros m mIn.
    inversion mIn.
Qed.

Lemma MPComp_zero_right : forall e, e ⊙ 𝟘 ≈ 𝟘.
Proof.
  intros e.
  unfold MPEqual.
  split.
  - unfold MPInclusion.
    intros m mIn.
    inversion mIn. subst. inversion H3.
  - unfold MPInclusion.
    intros m mIn.
    inversion mIn.
Qed.

Lemma MPComp_comm : forall e f, e ⊙ f ≈ f ⊙ e.
Proof.
  intros.
  unfold MPEqual;
  split;
  unfold MPInclusion; intros m mIn;
  inversion mIn as [ | | | | ? ? ? ? ? aIn bIn Eq |]; subst;
  econstructor; (apply bIn || apply aIn || rewrite Eq; apply mailbox_union_comm).
Qed.

Lemma MPComp_assoc : forall e f g, e ⊙ (f ⊙ g) ≈ (e ⊙ f) ⊙ g.
Proof.
  intros e f g.
  unfold MPEqual.
  split.
  - unfold MPInclusion.
    intros m mIn.
    inversion mIn as [ | | | | ? ? ? ? ? aIn bIn Eq |]; subst.
    inversion bIn as [ | | | | ? ? ? ? ? aIn' bIn' Eq' |]; subst.
    econstructor.
    + econstructor. apply aIn. apply aIn'. easy.
    + apply bIn'.
    + rewrite Eq. rewrite Eq'. now rewrite mailbox_union_assoc.
  - unfold MPInclusion.
    intros m mIn.
    inversion mIn as [ | | | | ? ? ? ? ? aIn bIn Eq |]; subst.
    inversion aIn as [ | | | | ? ? ? ? ? aIn' bIn' Eq' |]; subst.
    econstructor.
    + apply aIn'.
    + econstructor. apply bIn'. apply bIn. easy.
    + rewrite Eq. rewrite Eq'. now rewrite mailbox_union_assoc.
Qed.

Lemma MPComp_MPChoice_distr : forall e f g, e ⊙ (f ⊕ g) ≈ (e ⊙ f) ⊕ (e ⊙ g).
Proof.
  intros.
  unfold MPEqual.
  split; unfold MPInclusion; intros m mIn.
  - inversion mIn as [ | | | | ? ? ? ? ? aIn bIn Eq |]; subst;
    inversion bIn as [ | | e' f' m' mIn' | e' f' m' mIn' | | ]; subst.
    + apply MPValueChoiceLeft. econstructor. apply aIn. apply mIn'. apply Eq.
    + apply MPValueChoiceRight. econstructor. apply aIn. apply mIn'. apply Eq.
  - inversion mIn as [ | | e' f' m' mIn' | e' f' m' mIn' | | ]; subst;
    inversion mIn' as [ | | | | ? ? ? ? ? aIn bIn Eq |]; subst.
    + econstructor. apply aIn. apply MPValueChoiceLeft. apply bIn. apply Eq.
    + econstructor. apply aIn. apply MPValueChoiceRight. apply bIn. apply Eq.
Qed.

Lemma valueOf_One : forall m, m ∈ 𝟙 -> m = ⟨⟩.
Proof.
  intro m; unfold not; intros mIn; inversion mIn;
  subst; reflexivity.
Qed.

Lemma MPChoice_MPInclusion_One : forall e, e ⊑ 𝟙 ⊕ e.
Proof.
  unfold "⊑".
  intros e m mIn.
  now apply MPValueChoiceRight.
Qed.

Lemma MPComp_MPInclusion_One : forall e, e ⊑ e ⊙ 𝟙.
Proof.
  unfold "⊑".
  intros e m mIn.
  eapply MPValueComp.
  apply mIn.
  apply MPValueOne.
  now rewrite <- mailbox_union_empty_right.
Qed.

Lemma MPStar_MPInclusion_rec : forall e, ⋆ e ⊑ 𝟙 ⊕ (e ⊙ ⋆ e).
Proof.
  unfold "⊑".
  intros e m mIn.
  inversion mIn; subst.
  destruct H1 as [n pow].
  induction n; simpl in pow.
  - now apply MPValueChoiceLeft.
  - apply MPValueChoiceRight;
    inversion pow; subst;
    apply MPValueComp with (a := a) (b := b);
    try (easy);
    constructor; now exists n.
Qed.

Lemma MPStar_union : forall m a b e,
  m =ᵐᵇ a ⊎ b -> a ∈ e -> b ∈ ⋆ e -> m ∈ ⋆ e.
Proof.
  intros m a b e Eq aIn bIn.
  inversion bIn; subst.
  rename H1 into pow.
  destruct pow as [n pow].
  constructor.
  exists (S n). simpl.
  now apply MPValueComp with (a := a) (b := b).
Qed.

Lemma MPStar_valueOf_inv : forall m e, m ∈ e ⊙ ⋆ e -> m ∈ ⋆ e.
Proof.
  intros m e mIn.
  inversion mIn; subst.
  now apply MPStar_union with (a := a) (b := b).
Qed.

Lemma MPStar_rec : forall e, ⋆ e ≈ ⋆ e ⊕ e ⊙ ⋆ e.
Proof.
  intros e.
  unfold "≈".
  unfold "⊑".
  split.
  - now apply MPValueChoiceLeft.
  - intros m mIn.
    inversion mIn; subst.
    + easy.
    + now apply MPStar_valueOf_inv.
Qed.

Lemma MPInclusion_zero : forall e, e ⊑ 𝟘 -> e ≈ 𝟘.
Proof.
  intros e eSub.
  split.
  easy.
  intros m mIn.
  inversion mIn.
Qed.

Lemma valueOf_Message_Eq : forall m mc a b, a ∈ « m » -> ⟨ m ⟩ ⊎ mc =ᵐᵇ a ⊎ b -> mc =ᵐᵇ b.
Proof.
  intros * aIn Eq;
  inversion aIn; subst;
  eapply Permutation.Permutation_cons_inv;
  apply Eq.
Qed.

Lemma valueOf_MPComp_inv : forall m mc e, (⟨ m ⟩ ⊎ mc) ∈ « m » ⊙ e -> mc ∈ e.
Proof.
  intros * In.
  inversion In; subst.
  rewrite valueOf_Message_Eq with (a := a) (b := b) (m := m); easy.
Qed.

Lemma valueOf_Message_Res : forall mc m e e',
  (⟨ m ⟩ ⊎ mc) ∈ « m » ⊙ e ->
  « m » ⊙ e // « m » ~= e' ->
  mc ∈ e'.
Proof.
  intros * unionInE Res.
  apply valueOf_MPComp_inv in unionInE.
  inversion Res; subst.
  inversion H2; subst.
  - apply MPValueChoiceLeft.
    rewrite MPComp_comm.
    now rewrite MPComp_unit.
  - now destruct H1.
Qed.

Lemma valueOf_not_zero : forall mc e, mc ∈ e -> ~ e ≈ 𝟘.
Proof.
  intros * In.
  inversion In; subst; intros [Inc1 Inc2];
  generalize (Inc1 _ In);
  intros F; inversion F.
Qed.

Lemma MPInclusion_MPComp_Diff : forall n m f, ~ (f ⊑ 𝟘) -> m <> n -> ~ « n » ⊙ f ⊑ « m ».
Proof.
  intros *.
  intros notF Neq In.
  induction f; unfold "⊑" in *.
  - apply notF. easy.
  - generalize (In ⟨ n ⟩).
    intros InFalse.
    assert (In' : ⟨ n ⟩ ∈ « n » ⊙ 𝟙). apply MPComp_unit. constructor.
    apply InFalse in In'.
    inversion In'; subst. easy.
  - generalize (In (n :: m0 :: nil)).
    intros InFalse.
    assert (In' : (n :: m0 :: nil) ∈ « n » ⊙ « m0 »).
    {
      eapply MPValueComp with (a := ⟨ n ⟩) (b := ⟨ m0 ⟩);
      repeat constructor.
    }
    apply InFalse in In'.
    inversion In'.
  - apply notF. intros mc mcIn.
    generalize (In (⟨ n ⟩ ⊎ mc)).
    intros InFalse.
    assert (In' : (⟨ n ⟩ ⊎ mc) ∈ « n » ⊙ (f1 ⊕ f2)).
    {
      eapply MPValueComp with (a := ⟨ n ⟩).
      constructor.
      exact mcIn.
      repeat constructor. reflexivity.
    }
    apply InFalse in In'.
    inversion In'; subst. easy.
  - apply notF. intros mc mcIn.
    generalize (In (⟨ n ⟩ ⊎ mc)).
    intros InFalse.
    assert (In' : (⟨ n ⟩ ⊎ mc) ∈ « n » ⊙ (f1 ⊙ f2)).
    {
      eapply MPValueComp with (a := ⟨ n ⟩).
      constructor.
      exact mcIn.
      repeat constructor. reflexivity.
    }
    apply InFalse in In'.
    inversion In'; subst. easy.
  - apply notF. intros mc mcIn.
    generalize (In (⟨ n ⟩ ⊎ mc)).
    intros InFalse.
    assert (In' : (⟨ n ⟩ ⊎ mc) ∈ « n » ⊙ ⋆ f).
    {
      eapply MPValueComp with (a := ⟨ n ⟩).
      constructor.
      exact mcIn.
      repeat constructor. reflexivity.
    }
    apply InFalse in In'.
    inversion In'; subst. easy.
Qed.

Lemma MPValueChoice_inv : forall m e f g, m ∈ e -> e ⊑ f ⊕ g -> m ∈ f \/ m ∈ g.
Proof.
  intros * mIn Sub.
  apply Sub in mIn.
  inversion mIn; subst.
  - now left.
  - now right.
Qed.

Lemma Balancing_valueOf_message : forall mc m f,
  (⟨ m ⟩ ⊎ mc) ∈ « m » ⊙ f ->
  « m » ⊙ f // « m » ~= f ->
  mc ∈ f.
Proof.
  intros * In Res.
  inversion Res; subst.
  inversion H2; subst.
  - rewrite MPComp_comm.
    rewrite MPComp_unit.
    inversion In; subst.
    inversion H1; subst.
    apply Permutation.Permutation_app_inv_l in H7.
    rewrite H7.
    now apply MPValueChoiceLeft.
  - now destruct H1.
Qed.

Lemma Balancing_valueOf' : forall mc m f f',
  (⟨ m ⟩ ⊎ mc) ∈ « m » ⊙ f ->
  « m » ⊙ f // « m » ~= f' ->
  mc ∈ f'.
Proof.
  intros * In Res.
  inversion Res; subst.
  inversion H2; subst.
  - rewrite MPComp_comm.
    rewrite MPComp_unit.
    inversion In; subst.
    inversion H1; subst.
    apply Permutation.Permutation_app_inv_l in H6.
    rewrite H6.
    now apply MPValueChoiceLeft.
  - now destruct H1.
Qed.

Lemma in_split_valueOf : forall m a e, In m a -> a ∈ e -> exists a', (⟨ m ⟩ ⊎ a') ∈ e.
Proof.
  intros * In valueOf.
  generalize (in_split m a In).
  intros [l1 [l2 Eq]].
  subst.
  rewrite <- Permutation.Permutation_middle in valueOf.
  exists (l1 ++ l2).
  easy.
Qed.

Lemma MPValueStar_split : forall m mc e,
  (⟨ m ⟩ ⊎ mc) ∈ ⋆ e ->
  exists a b, ((⟨ m ⟩ ⊎ a) ∈ e) /\ (b ∈ ⋆ e) /\ mc =ᵐᵇ a ⊎ b.
Proof.
  intros * In.
  inversion In; subst.
  destruct H1 as [n In'].
  revert mc In In'.
  induction n; intros * In In'.
  - simpl in In'; inversion In'.
  - simpl in In'.
    inversion In'; subst.
    remember H4 as Eq.
    clear HeqEq.
    apply mailbox_eq_union_split in H4.
    destruct H4 as [[a' Eq'] | [b' Eq']].
    + exists a', b; repeat split.
      * rewrite Eq in Eq'.
        apply Permutation.Permutation_app_inv_r in Eq'.
        now rewrite Eq' in H1.
      * constructor. now exists n.
      * intros. simpl in Eq'.
        now apply Permutation.Permutation_app_inv_l with (l := ⟨ m ⟩) in Eq'.
    + remember Eq' as EqOrig.
      clear HeqEqOrig.
      rewrite Eq in Eq'.
      rewrite Permutation.Permutation_app_comm with (l' := a) in Eq'.
      rewrite <- app_assoc in Eq'.
      apply Permutation.Permutation_app_inv_l with (l := a) in Eq'.
      assert (InStar : (⟨ m ⟩ ⊎ b') ∈ ⋆ e).
      {
        constructor. exists n. now rewrite <- Eq'.
      }
      rewrite Eq' in H3.
      generalize (IHn b' InStar H3).
      intros [a'' [b'' [In'' [InStar' Eq'']]]].
      exists a'', (a ⊎ b''); repeat split.
      * assumption.
      * inversion InStar'; subst.
        destruct H2 as [n' Pow'].
        constructor. exists (S n').
        simpl.
        eapply MPValueComp.
        -- exact H1.
        -- exact Pow'.
        -- reflexivity.
      * rewrite app_assoc.
        rewrite Permutation.Permutation_app_comm with (l' := b'').
        rewrite app_assoc.
        rewrite Permutation.Permutation_app_comm with (l' := a'').
        rewrite <- Eq''.
        simpl in EqOrig.
        apply Permutation.Permutation_app_inv_l with (l := ⟨ m ⟩) in EqOrig.
        rewrite Permutation.Permutation_app_comm.
        assumption.
Qed.

Lemma Balancing_valueOf : forall mc m f f',
  (⟨ m ⟩ ⊎ mc) ∈ f ->
  f // « m » ~= f' ->
  mc ∈ f'.
Proof.
  intros *.
  revert mc m f'.
  induction f; intros * In Res.
  - inversion In.
  - inversion In.
  - inversion In; subst.
    inversion Res; subst.
    constructor.
    now destruct H1.
  - inversion Res; subst.
    inversion In; subst.
    + apply MPValueChoiceLeft.
      eapply IHf1.
      exact H1.
      exact H2.
    + apply MPValueChoiceRight.
      eapply IHf2.
      exact H1.
      exact H4.
  - inversion Res; subst.
    inversion In; subst.
    remember H6 as Eq.
    clear HeqEq.
    apply mailbox_eq_union_split in H6.
    destruct H6 as [[a' Eq'] | [b' Eq']].
    + apply MPValueChoiceLeft.
      eapply MPValueComp with (a := a') (b := b).
      * apply IHf1 with (m := m).
        rewrite Eq' in Eq.
        apply Permutation.Permutation_app_inv_r in Eq.
        now rewrite Eq.
        assumption.
      * assumption.
      * eapply Permutation.Permutation_app_inv_l with (l := (m :: nil)).
        apply Eq'.
    + apply MPValueChoiceRight.
      eapply MPValueComp with (a := a) (b := b').
      * assumption.
      * apply IHf2 with (m := m).
        rewrite Eq' in Eq.
        rewrite Permutation.Permutation_app_comm with (l' := a) in Eq.
        rewrite <- app_assoc in Eq.
        apply Permutation.Permutation_app_inv_l in Eq.
        now rewrite Eq.
        assumption.
      * eapply Permutation.Permutation_app_inv_l with (l := (m :: nil)).
        apply Eq'.
  - inversion Res; subst.
    inversion In; subst.
    destruct H2 as [n In'].
    apply MPValueStar_split in In.
    destruct In as [a [b [InF [InStar Eq]]]].
    rewrite Eq.
    generalize (IHf a m e' InF H1).
    intros InE'.
    eapply MPValueComp.
    + exact InE'.
    + exact InStar.
    + reflexivity.
Qed.

Lemma PatternResidual_det : forall m e f f', e // « m » ~= f -> e // « m » ~= f' -> f = f'.
Proof.
  intro m.
  induction e; intros * Res1 Res2.
  - inversion Res1; subst; inversion Res2; subst; reflexivity.
  - inversion Res1; subst; inversion Res2; subst; reflexivity.
  - inversion Res1; subst; inversion Res2; subst;
    try (reflexivity; fail);
    try (now destruct H1).
  - inversion Res1; subst; inversion Res2; subst.
    generalize (IHe1 _ _ H2 H3); intros ->;
    generalize (IHe2 _ _ H4 H6); intros ->;
    reflexivity.
  - inversion Res1; subst; inversion Res2; subst.
    generalize (IHe1 _ _ H2 H3); intros ->;
    generalize (IHe2 _ _ H4 H6); intros ->;
    reflexivity.
  - inversion Res1; subst; inversion Res2; subst.
    generalize (IHe e' e'0 H1 H2); intros ->;
    reflexivity.
Qed.

Lemma PatternResidual_MPComp : forall m f f' e, « m » ⊙ f // « m » ~= e -> f // « m » ~= f' -> e ≈ f ⊕ « m » ⊙ f'.
Proof.
  intros * Res1 Res2.
  inversion Res1; subst.
  inversion H2; subst.
  - rewrite MPComp_comm.
    rewrite MPComp_unit.
    rewrite (PatternResidual_det m f f' f'0).
    + reflexivity.
    + assumption.
    + assumption.
  - now destruct H1.
Qed.

(** Balancing lemma
    Proof based on Ugo de’Liguoro and Luca Padovani Prop. 27
    In Fowler et al. this is Lemma D.8
*)
Lemma Balancing : forall m f e e', « m » ⊙ f ⊑ e -> ~ (f ⊑ 𝟘) -> e // « m » ~= e' -> f ⊑ e'.
Proof.
  intros * Sub NotSub0 Res mc mcIn.
  assert (In' : (⟨ m ⟩ ⊎ mc) ∈ « m » ⊙ f).
  {
    eapply MPValueComp with (a := ⟨ m ⟩) (b := mc).
    constructor. exact mcIn. reflexivity.
  }
  apply Sub in In'.
  apply Balancing_valueOf with (m := m) (f := e); assumption.
Qed.


End MPattern_props.

Require Import String.
Open Scope string_scope.

(** Some examples *)

Example Test : ⟨⟩ ∈ (𝟙 ⊕ 𝟘).
Proof.
  apply MPValueChoiceLeft.
  apply MPValueOne.
Qed.

Example Test1 : (⟨ "m" ⟩ ⊎ ⟨ "n" ⟩) ∈ (« "n" » ⊙ « "m" »).
Proof.
  eapply MPValueComp.
  - apply MPValueMessage.
  - apply MPValueMessage.
  - now rewrite mailbox_union_comm.
Qed.

(* TODO: Some proper relation proof is missing to prove this 
Example Test2 : MPEqual (𝟙 ⊕ 𝟘 ⊕ (« "m" » ⊙ « "n" »)) (𝟙 ⊕ (« "n" » ⊙ « "m" »)).
Proof.
Admitted.
*)
