(** * Syntax of types *)

From Stdlib Require Import Lia.
From Stdlib Require Import Classes.RelationClasses.

From MailboxTypes Require Export Message.
From MailboxTypes Require Export MailboxPatterns.

From Stdlib Require Import List.
Import ListNotations.
Require Import Classes.RelationClasses.
Require Import Classes.Morphisms.

Generalizable All Variables.

Section type_def.

Context `{M : IMessage Message}.

(** Mailbox type definition *)
Inductive MType : Type :=
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

Definition BaseType (T : TType) : Prop :=
  match T with
  | TTBase _ => True
  | _ => False
  end.

(** A list of only base types *)
Fixpoint BaseTypes (e : list TType) : Prop :=
  match e with
  | nil => True
  | (TTBase _ :: e') => BaseTypes e'
  | _ => False
  end.

Inductive ReturnableType : TUsage -> Prop :=
  | ReturnableBase : forall c, ReturnableType (TUBase c)
  | ReturnableUsage : forall T, ReturnableType (TUUsage Returnable T).

Inductive SecondType : TUsage -> Prop :=
  | SecondBase : forall c, SecondType (TUBase c)
  | SecondUsage : forall T, SecondType (TUUsage SecondClass T).

Inductive UsageSubtype : UsageAnnotation -> UsageAnnotation -> Prop :=
    UsageSubtypeRefl : forall n, UsageSubtype n n
  | UsageSubtypeLe   : UsageSubtype Returnable SecondClass.

Inductive Subtype : TUsage -> TUsage -> Prop :=
    SubtypeBase : forall c, Subtype (TUBase c) (TUBase c)
  | SubtypeInput : forall e f n1 n2,
      MPInclusion e f -> UsageSubtype n1 n2 -> Subtype (TUUsage n1 (MTInput e)) (TUUsage n2 (MTInput f))
  | SubtypeOutput : forall e f n1 n2,
      MPInclusion f e -> UsageSubtype n1 n2 -> Subtype (TUUsage n1 (MTOutput e)) (TUUsage n2 (MTOutput f)).

Inductive RuntimeSubtype : TType -> TType -> Prop :=
    RuntimeSubtypeBase : forall c, RuntimeSubtype (TTBase c) (TTBase c)
  | RuntimeSubtypeInput : forall e f,
      MPInclusion e f -> RuntimeSubtype (TTMailbox (MTInput e)) (TTMailbox (MTInput f))
  | RuntimeSubtypeOutput : forall e f,
      MPInclusion f e -> RuntimeSubtype (TTMailbox (MTOutput e)) (TTMailbox (MTOutput f)).

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

Definition Relevant (m : MType) : Prop :=
  forall n, ~ ((TUUsage n m) ≤ (TUUsage n (! 𝟙))).

Definition Irrelevant (m : MType) : Prop :=
  forall n, (m ^^ n) ≤ (! 𝟙 ^^ n).

Definition Reliable (m : MType) : Prop :=
  forall n, ~ ((TUUsage n m) ≤ (TUUsage n (? 𝟘))).

Definition Unreliable (m : MType) : Prop :=
  ~ Reliable m.

Definition Usable (m : MType) : Prop :=
  forall n, ~ ((TUUsage n m) ≤ (TUUsage n (! 𝟘))).

Definition Unusable (m : MType) : Prop :=
  ~ Usable m.

(* TODO: Check if this is correct *)

(* Old Version *)
(*Inductive Unrestricted : TUsage -> Prop :=*)
(*    unBase : forall c : BType, Unrestricted (TUBase c)*)
(*  | unOne : Unrestricted (TUUsage SecondClass (! 𝟙)).*)

(** In the original paper, the predicate Unrestricted is defined over a syntactic
    check, i.e. Un(T) <=> T = ! 𝟙 ^^ ◦.

    However, this definition breaks transitivity of environment subtyping. As an
    example, consider environment [[! 𝟙 ^^ •]]. The type [! 𝟙 ^^ •] is not unrestricted,
    so, [[! 𝟙 ^^ •] ≤ₑ []] does not hold. But [! 𝟙 ^^ • ≤ ! 𝟙 ^^ ◦] holds, and 
    [[! 𝟙 ^^ ◦] ≤ₑ []] holds since the type is unrestricted.

    So in the typing rules we would have to use the [TSub]-rule twice in order to
    weaken the environment from [[! 𝟙 ^^ •]] to [[]].
    To avoid this, we define a type to be unrestricted, if it is a subtype of [! 𝟙 ^^ ◦].
*)

Inductive Unrestricted : TUsage -> Prop :=
    unBase : forall c : BType, Unrestricted (TUBase c)
  | unOne : Unrestricted (! 𝟙 ^^ ◦).

Definition Linear (m : TUsage) : Prop :=
  ~ Unrestricted m.

(** A cruft type is either a base type or irrelevant.
    A cruft type represents a type that can be added
   through the subtyping rule which may not be used
   by a term.
*)
(* TODO: Maybe we should define a cruft type as one which super type is 𝟙?*)
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

  Inductive PatternEq : MPattern -> MPattern -> Prop :=
    | PatternEqRefl : forall e, PatternEq e e
    | PatternEqComm : forall e f, PatternEq (e ⊙ f) (f ⊙ e)
    | PatternEqAssoc : forall e f g, PatternEq (e ⊙ (f ⊙ g)) ((e ⊙ f) ⊙ g)
    | PatternEqSkip : forall e f g, PatternEq f g -> PatternEq (e ⊙ f) (e ⊙ g)
    | PatternEqSym : forall e f, PatternEq e f -> PatternEq f e
    | PatternEqTrans : forall e f g, PatternEq e f -> PatternEq f g -> PatternEq e g.

  Inductive TypeEq : TType -> TType -> Prop :=
    | TypeEqBase : forall b, TypeEq (TTBase b) (TTBase b)
    | TypeEqInput : forall e f,
        PatternEq e f -> TypeEq (TTMailbox (! e)) ((TTMailbox (! f)))
    | TypeEqOutput : forall e f,
        PatternEq e f -> TypeEq (TTMailbox (? e)) ((TTMailbox (? f))).

(** 
   Definition 3.5 of type combiniations. Instead of defining it as a partial function,
   we define it as a relation between three types.
*)
  Inductive TypeCombination : TType -> TType -> TType -> Prop :=
      TCombBase : forall c, TypeCombination (TTBase c) (TTBase c) (TTBase c)
    | TCombOut : forall e f, TypeCombination (TTMailbox (! e)) (TTMailbox (! f)) (TTMailbox (! (e ⊙ f)))
    | TCombInOut : forall e f, TypeCombination (TTMailbox (! e)) (TTMailbox (? (e ⊙ f))) (TTMailbox (? f))
    | TCombOutIn : forall e f, TypeCombination (TTMailbox (? (e ⊙ f))) (TTMailbox (! e)) (TTMailbox (? f))
    | TCombEq : forall T1 T1' T2 T2' T3 T3',
        TypeEq T1 T1' ->
        TypeEq T2 T2' ->
        TypeEq T3 T3' ->
        TypeCombination T1 T2 T3 ->
        TypeCombination T1' T2' T3'.

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


Section mailbox_types_properties.
  Context `{M : IMessage Message}.

  Lemma secondUsage_idem : forall T, ⌈ T ⌉ⁿ = ⌈ ⌈ T ⌉ⁿ ⌉ⁿ.
  Proof.
    destruct T; try destruct b; easy.
  Qed.

  (** Subtyping preserves reliability.
      Proof based on Ugo de’Liguoro and Luca Padovani Prop. 26
      In Fowler et al. this is Lemma D.6
  *)
  Lemma SubtypeReliable : forall a b n1 n2, (a ^^ n1) ≤ (b ^^ n2) -> Reliable a -> Reliable b.
  Proof.
    intros a b n1 n2 Sub_a Rel.
    unfold Reliable in *.
    destruct a; inversion Sub_a as [| ? ? ? ? Inc_mf |]; subst;
    intros n Sub_b; inversion Sub_b as [| ? ? ? ? Inc_f0 |]; subst.
    generalize (MPInclusion_trans m f 𝟘 Inc_mf Inc_f0).
    intros Inc0.
    destruct Rel with (n := n).
    constructor; easy.
  Qed.

  (** Subtyping preserves usability.
      Proof based on Ugo de’Liguoro and Luca Padovani Prop. 26
      In Fowler et al. this is Lemma D.6
  *)
  Lemma SubtypeUsable : forall a b n1 n2, (a ^^ n1) ≤ (b ^^ n2) -> Usable a -> Usable b.
  Proof.
    intros a b n1 n2 Sub_a Use.
    unfold Usable in *.
    destruct a; inversion Sub_a as [| | ? ? ? ? Inc_fm ]; subst;
    intros n Sub_b; inversion Sub_b as [| | ? ? ? ? Inc_0f]; subst.
    generalize (MPInclusion_trans 𝟘 f m Inc_0f Inc_fm).
    intros Inc0.
    destruct Use with (n := n).
    constructor; easy.
Qed.

Lemma UsageSubtype_trans : forall n1 n2 n3, n1 ≤ⁿ n2 -> n2 ≤ⁿ n3 -> n1 ≤ⁿ n3.
Proof.
  intros * Sub1 Sub2; destruct n1, n2, n3; try (constructor); assumption.
Qed.

Global Instance UsageSubtype_refl : Reflexive UsageSubtype.
Proof.
  unfold Reflexive; constructor.
Qed.

Lemma Subtype_refl : forall t, t ≤ t.
Proof.
  destruct t.
  - constructor.
  - destruct m; constructor; try (apply MPInclusion_refl || constructor).
Qed.

Lemma Subtype_trans : forall t1 t2 t3, t1 ≤ t2 -> t2 ≤ t3 -> t1 ≤ t3.
Proof.
  intros * Sub1 Sub2.
  induction Sub1; inversion Sub2; subst; constructor;
  try (
    now apply MPInclusion_trans with (f := f) ||
    now apply UsageSubtype_trans with (n2 := n2)
  ).
Qed.

Lemma Subtype_inversion_TUBase_right : forall T B, T ≤ (TUBase B) -> T = TUBase B.
Proof.
  intros * Sub.
  now inversion Sub.
Qed.

Lemma Subtype_inversion_TUBase_left : forall T B, (TUBase B) ≤ T -> T = TUBase B.
Proof.
  intros * Sub.
  now inversion Sub.
Qed.

Lemma TypeCombination_comm : forall T1 T2 T3, T1 ⊞ T2 ~= T3 -> T2 ⊞ T1 ~= T3.
Proof.
  intros * Comb.
  induction Comb; try constructor.
  - econstructor; constructor.
    + apply PatternEqRefl.
    + apply PatternEqRefl.
    + apply PatternEqComm.
  - econstructor; eassumption.
Qed.

Lemma TypeEq_sym : forall T1 T2, TypeEq T1 T2 -> TypeEq T2 T1.
Proof.
  intros; inversion H; subst; try apply PatternEqSym in H0; now constructor.
Qed.

Global Instance PatternEq_equiv : Equivalence PatternEq.
Proof.
  constructor; constructor.
  assumption.
  generalize (PatternEqTrans _ _ _ H H0).
  intros. now apply PatternEqSym.
Qed.


Global Instance MPComp_PatternEq_Proper : Proper (TypeEq ==> TypeEq ==> TypeEq ==> iff) TypeCombination.
Proof.
  intros T1 T2 Eq1 T1' T2' Eq' T1'' T2'' Eq''.
  split; intros Comb; econstructor; try eassumption; apply TypeEq_sym; assumption.
Qed.

Lemma TypeEq_trans : forall T1 T2 T3, TypeEq T1 T2 -> TypeEq T2 T3 -> TypeEq T1 T3.
Proof.
  intros * Eq1 Eq2.
  inversion Eq1; subst; inversion Eq2; subst;
  constructor; eapply PatternEqTrans; eassumption.
Qed.

Lemma TypeEq_refl : forall T, TypeEq T T.
Proof.
  intros.
  destruct T; try constructor.
  destruct m; constructor; reflexivity.
Qed.

Global Instance TypeEq_equiv : Equivalence TypeEq.
Proof.
  constructor.
  - intros T; apply TypeEq_refl.
  - intros T1 T2 Eq; now apply TypeEq_sym.
  - intros T1 T2 T3 Eq1 Eq2; eapply TypeEq_trans; eassumption.
Qed.

Lemma TypeCombination_Base_inv : forall T1 T2 c,
  T1 ⊞ T2 ~= TTBase c ->
  T1 = TTBase c /\ T2 = TTBase c.
Proof.
  intros * Comb.
  remember (TTBase c) as C.
  revert c HeqC.
  induction Comb; intros; try inversion HeqC; subst.
  - auto.
  - inversion H1; subst.
    generalize (IHComb c eq_refl).
    intros [-> ->].
    inversion H; subst.
    inversion H0; subst.
    auto.
Qed.

Lemma PatternEq_1 : forall e f0 e0, PatternEq ((e ⊙ f0) ⊙ e0) (e ⊙ (e0 ⊙ f0)).
Proof.
  intros.
  eapply PatternEqTrans.
  - apply PatternEqSym. apply PatternEqAssoc.
  - apply PatternEqSkip. constructor.
Qed.

Lemma PatternEq_2 : forall e e0 f, PatternEq (e ⊙ (e0 ⊙ f)) (e0 ⊙ (e ⊙ f)).
Proof.
  intros.
  eapply PatternEqTrans.
  - apply PatternEqComm.
  - eapply PatternEqTrans.
    + apply PatternEqSym. apply PatternEqAssoc.
    + apply PatternEqSkip. constructor.
Qed.

(* TODO: Extend this tactic *)
Ltac solve_PatternEq :=
  match goal with
  | H : _ |- PatternEq ((?e ⊙ ?f) ⊙ ?g) (?e ⊙ (?g ⊙ ?f)) =>
    apply PatternEq_1
  | H : _ |- PatternEq (?e ⊙ (?f ⊙ ?g)) (?f ⊙ (?e ⊙ ?g)) =>
    apply PatternEq_2
  | H : _ |- PatternEq (?e ⊙ ?f) (?e ⊙ ?g) =>
      apply PatternEqSkip
  end;
  try (constructor; fail).

Lemma TypeCombination_assoc : forall T1 T2 T2' T3 T,
  T1 ⊞ T2' ~= T ->
  T2 ⊞ T3 ~= T2' ->
  exists T1', T1' ⊞ T3 ~= T /\ T1 ⊞ T2 ~= T1'.
Proof.
  intros * Comb1.
  revert T2 T3.
  induction Comb1; intros * Comb2; inversion Comb2; subst;
  try match goal with
  | H : _ ⊞ _ ~= TTBase ?c |- _ =>
    apply TypeCombination_Base_inv in H;
    destruct H; subst;
    exists (TTBase c); split; constructor
  end.
  - exists (TTMailbox (! e ⊙ e0)); split.
    + eapply TCombEq; constructor; try apply PatternEqRefl.
      apply PatternEqSym.
      apply PatternEqAssoc.
    + constructor.
  - inversion H1; subst.
    revert e f T3 T2 H0 H H1 H5 Comb2.
    induction H2; intros; try (inversion H1; fail); subst.
    + subst.
      inversion H0; subst.
      inversion H; subst.
      inversion H1; subst.
      exists (TTMailbox (! e1 ⊙ e)); split.
      * eapply TCombEq; constructor.
        -- apply PatternEqRefl.
        -- eassumption.
        -- apply PatternEqSkip with (e := e1) in H7.
           eapply PatternEqTrans.
           apply PatternEqSym.
           apply PatternEqAssoc.
           assumption.
      * eapply TCombEq; constructor.
        -- apply PatternEqRefl.
        -- eassumption.
        -- constructor.
    + now generalize (IHTypeCombination e f T0 T4
        (TypeEq_trans _ _ _ H0 H3)
        (TypeEq_trans _ _ _ H H4)
        (TypeEq_trans _ _ _ H1 H5)
        H6 Comb2
      ).
  - exists (TTMailbox (! e0 ⊙ e)); split.
    + econstructor; constructor.
      * constructor.
      * apply PatternEqSym. apply PatternEqAssoc.
      * constructor.
    + econstructor; constructor;
      try apply PatternEqRefl.
      constructor.
  - exists (TTMailbox (? e0 ⊙ f)); split.
    + constructor.
    + econstructor; constructor;
      try apply PatternEqRefl.
      solve_PatternEq.
  - inversion H1; subst.
    revert e f T2 T3 H H0 H1 H5 Comb2.
    induction H2; intros; try (inversion H1; fail); subst.
    + inversion H; subst.
      inversion H0; subst.
      inversion H1; subst.
      exists (TTMailbox (! e1 ⊙ e)); split.
      * eapply TCombEq; constructor.
        -- apply PatternEqRefl.
        -- rewrite <- H4.
           eapply PatternEqTrans.
           ++ apply PatternEqSym. apply PatternEqAssoc.
           ++ eapply PatternEqTrans.
              ** apply PatternEqComm.
              ** eapply PatternEqTrans.
                 apply PatternEqSym. apply PatternEqAssoc.
                 apply PatternEqSkip.
                 rewrite H7.
                 apply PatternEqComm.
        -- constructor.
      * econstructor; constructor; try apply PatternEqRefl.
        now apply PatternEqSkip.
    + inversion H; subst.
      inversion H0; subst.
      inversion H1; subst.
      exists (TTMailbox (? e ⊙ f0)); split.
      * econstructor; try constructor.
        -- apply PatternEqRefl.
        -- eassumption.
        -- apply PatternEqRefl.
      * eapply TCombEq with (T1 := TTMailbox (! e1)) (T2 := TTMailbox (? e ⊙ (e1 ⊙ f0)));
        try constructor.
        -- constructor.
        -- rewrite <- H3.
           apply PatternEqSkip.
           now rewrite H7.
        -- econstructor.
        -- econstructor; try constructor.
           ++ constructor.
           ++ apply PatternEqSym.
              eapply PatternEqTrans.
              ** apply PatternEqComm.
              ** apply PatternEqSym. apply PatternEqAssoc.
           ++ constructor.
    + inversion H5; subst.
      inversion H1; subst.
      apply IHTypeCombination.
      * eauto using TypeEq_trans.
      * eauto using TypeEq_trans.
      * constructor; rewrite H10; now rewrite H9.
      * assumption.
      * assumption.
  - exists (TTMailbox (? f0 ⊙ f)); split.
    + constructor.
    + econstructor; constructor.
      * apply PatternEqAssoc.
      * constructor.
      * constructor.
  - inversion H1; subst.
    revert e f T2 T3 H H0 H1 H5 Comb2.
    induction H2; intros; try (inversion H1; fail); subst.
    + inversion H; subst.
      inversion H0; subst.
      inversion H1; subst.
      exists (TTMailbox (? f ⊙ f0)); split.
      * econstructor.
        reflexivity.
        eassumption.
        reflexivity.
        constructor.
      * eapply TCombEq with (T1 := TTMailbox (? e ⊙ (f ⊙ f0))) (T2 := TTMailbox (! e)).
        -- constructor.
           eapply PatternEqTrans.
           apply PatternEqAssoc.
           eapply PatternEqTrans.
           apply PatternEqComm.
           apply PatternEqSym.
           eapply PatternEqTrans.
           apply PatternEqComm.
           now apply PatternEqSkip.
        -- assumption.
        -- reflexivity.
        -- constructor.
    + apply IHTypeCombination; try assumption;
      eauto using TypeEq_trans.
  - inversion H0; subst.
    generalize (IHComb1 (TTBase c) (TTBase c) (TCombBase c)).
    intros [T1'' [Comb1' Comb2']].
    exists T1''; split; econstructor; eauto; reflexivity.
  - inversion H0; subst.
    assert (TTMailbox (! e) ⊞ TTMailbox (! f) ~= TTMailbox (! e0 )).
    {
      econstructor; constructor.
      constructor.
      constructor.
      now apply PatternEqSym.
    }
    generalize (IHComb1 _ _ H2).
    intros [T1'' [Comb1' Comb2']].
    exists (T1''); split.
    + eapply TCombEq with (T3 := T3); try reflexivity; assumption.
    + eapply TCombEq with (T1 := T1); try reflexivity; assumption.
  - inversion H0; subst.
    assert (TTMailbox (! e) ⊞ TTMailbox (? e ⊙ f) ~= TTMailbox (? e0 )).
    {
      econstructor; try constructor.
      reflexivity.
      reflexivity.
      apply PatternEqSym; eassumption.
    }
    generalize (IHComb1 _ _ H2).
    intros [T1'' [Comb1' Comb2']].
    exists (T1''); split.
    + eapply TCombEq with (T3 := T3); try reflexivity; assumption.
    + eapply TCombEq with (T1 := T1); try reflexivity; assumption.
  - inversion H0; subst.
    assert (TTMailbox (? e ⊙ f) ⊞ TTMailbox (! e) ~= TTMailbox (? e0 )).
    {
      econstructor; try constructor.
      reflexivity.
      reflexivity.
      apply PatternEqSym; eassumption.
    }
    generalize (IHComb1 _ _ H2).
    intros [T1'' [Comb1' Comb2']].
    exists (T1''); split.
    + eapply TCombEq with (T3 := T3); try reflexivity; assumption.
    + eapply TCombEq with (T1 := T1); try reflexivity; assumption.
  - assert (T0 ⊞ T4 ~= T2).
    {
      econstructor.
      reflexivity.
      reflexivity.
      symmetry. eassumption.
      assumption.
    }
    generalize (IHComb1 T0 T4 H6).
    intros [T1'' [Comb1' Comb2']].
    exists (T1''); split.
    + eapply TCombEq with (T3 := T3); try reflexivity; assumption.
    + eapply TCombEq with (T1 := T1); try reflexivity; assumption.
Qed.

Lemma TypeCombination_TTMailbox_inv_left : forall T1 T2 T,
  T1 ⊞ T2 ~= TTMailbox T ->
  exists T1', T1 = TTMailbox T1'.
Proof.
  intros * Comb.
  remember (TTMailbox T) as TT.
  revert T HeqTT.
  induction Comb; intros; inversion HeqTT; subst; eauto.
  inversion H1; subst.
  1: generalize (IHComb (! e) eq_refl).
  2: generalize (IHComb (? e) eq_refl).
  all :
    intros [T1'' Eq]; subst;
    inversion H; subst;
    try (now exists (! f0));
    now exists (? f0).
Qed.

Lemma TypeUsageCombination_assoc : forall T1 T2 T2' T3 T,
  T1 ▷ T2' ~= T ->
  T2 ▷ T3 ~= T2' ->
  exists T1', T1' ▷ T3 ~= T /\ T1 ▷ T2 ~= T1'.
Proof.
  intros * Comb1 Comb2.
  inversion Comb1; inversion Comb2; subst.
  - inversion H4; subst.
    exists (TUBase c); auto.
  - inversion H6.
  - inversion H6.
  - inversion H8; subst.
    generalize (TypeCombination_assoc _ _ _ _ _ H0 H5).
    intros [T' [Comb1' Comb2']].
    generalize (TypeCombination_TTMailbox_inv_left _ _ _ Comb1').
    intros [T1' ->].
    inversion H; subst.
    + inversion H4; subst.
      exists (T1' ^^ ◦); split; constructor; auto.
    + inversion H4; subst.
      exists (T1' ^^ ◦); split; constructor; auto. constructor.
Qed.

Lemma TypeCombination_assoc_left : forall T1 T1' T2 T3 T,
  T1' ⊞ T2 ~= T ->
  T1 ⊞ T3 ~= T1' ->
  exists T2', T1 ⊞ T2' ~= T /\ T2 ⊞ T3 ~= T2'.
Proof.
  intros * Comb1 Comb2.
  apply TypeCombination_comm in Comb1.
  apply TypeCombination_comm in Comb2.
  generalize (TypeCombination_assoc _ _ _ _ _ Comb1 Comb2).
  intros [T' [Comb1' Comb2']].
  exists T'; split.
  - now apply TypeCombination_comm.
  - assumption.
Qed.

Lemma TypeUsageCombination_assoc_left : forall T1 T1' T2 T3 T,
  T1' ▷ T3 ~= T ->
  T1 ▷ T2 ~= T1' ->
  exists T3', T1 ▷ T3' ~= T /\ T2 ▷ T3 ~= T3'.
Proof.
  intros * Comb1 Comb2.
  inversion Comb1; inversion Comb2; subst.
  - inversion H4; subst; now exists (TUBase c).
  - inversion H6.
  - inversion H6.
  - inversion H8; subst.
    generalize (TypeCombination_assoc_left _ _ _ _ _ H0 H5).
    intros [T' [Comb1' Comb2']].
    apply TypeCombination_comm in Comb1'.
    generalize (TypeCombination_TTMailbox_inv_left _ _ _ Comb1').
    intros [T1' ->].
    apply TypeCombination_comm in Comb1'.
    apply TypeCombination_comm in Comb2'.
    inversion H; subst.
    + inversion H4; subst.
      exists (T1' ^^ ◦); split; constructor; auto.
    + inversion H4; subst.
      exists (T1' ^^ •); split; constructor; auto.
Qed.

Lemma Unrestricted_implies_Cruft : forall T, Unrestricted T -> TUCruft T.
Proof.
  intros * Unr; inversion Unr; constructor; reflexivity.
Qed.

Lemma Subtype_Irrelevant : forall T1 T2 n1 n2,
  Irrelevant T2 -> T1 ^^ n1  ≤ T2 ^^ n2 -> Irrelevant T1.
Proof.
  intros * Irr Sub.
  unfold Irrelevant in *.
  intros n'.
  inversion Sub; subst.
  - inversion H4; subst.
    + generalize (Irr SecondClass); intros I; inversion I.
    + generalize (Irr SecondClass); intros I; inversion I.
  - destruct n'.
    assert (SubSecond : ! e ^^ ◦ ≤ ! f ^^ ◦) by now constructor.
    eauto using Subtype_trans.
    assert (SubReturn : ! e ^^ • ≤ ! f ^^ •) by now constructor.
    eauto using Subtype_trans.
Qed.

Lemma Subtype_Second : forall T1 T2,
  SecondType T1 ->
  T1 ≤ T2 ->
  SecondType T2.
Proof.
  intros * S Sub.
  destruct T1; inversion Sub; inversion S; subst.
  - constructor.
  - inversion H3; subst; constructor.
  - inversion H3; subst; constructor.
Qed.

Lemma Subtype_Returnable : forall T1 T2,
  T1 ≤ T2 ->
  ReturnableType T2 ->
  ReturnableType T1.
Proof.
  intros * Sub Ret.
  destruct T2; inversion Sub; subst.
  - constructor.
  - inversion Ret; subst.
    inversion H3; subst.
    constructor.
  - inversion Ret; subst.
    inversion H3; subst.
    constructor.
Qed.

(** Leibniz equality of mailbox types is decidable *)
Lemma MType_eq_dec : forall (T1 T2 : MType), {T1 = T2} + {T1 <> T2}.
Proof.
  destruct T1 as [m1 | m1], T2 as [m2 | m2];
  try (right; intros N; discriminate);
  case (MPattern_eq_dec m1 m2); intros Eq; subst;
  try (now left);
  right; intros N; now inversion N.
Qed.

(** Leibniz equality of types is decidable *)
Lemma TType_eq_dec : forall (T1 T2 : TType), {T1 = T2} + {T1 <> T2}.
Proof.
  destruct T1, T2;
  try (right; intros N; discriminate).
  - destruct b, b0;
    try (now left);
    try (right; intros N; discriminate).
  - case (MType_eq_dec m m0); intros; subst.
    now left.
    right; intros N; now inversion N.
Qed.

(** Leibniz equality of usage types is decidable *)
Lemma TUsage_eq_dec : forall (T1 T2 : TUsage), {T1 = T2} + {T1 <> T2}.
Proof.
  destruct T1, T2;
  try (right; intros N; discriminate).
  - destruct b, b0;
    try (now left);
    try (right; intros N; discriminate).
  - destruct u, u0;
    try (right; intros N; discriminate);
    case (MType_eq_dec m m0); intros; subst;
    try (now left);
    try (right; intros N; now inversion N).
Qed.

(** Deciding whether a type is unrestricted is deciable *)
Lemma Unrestricted_dec : forall T, {Unrestricted T} + {~ Unrestricted T}.
Proof.
  intros T; destruct T.
  - left; constructor.
  - destruct m; destruct m; destruct u;
    try (left; constructor);
    right; intros Unr; inversion Unr.
Qed.

(*Lemma asdgdf : forall e1 e2, e1 ⊙ e2 ⊑ 𝟙 -> e1 ≈ 𝟙 /\ e2 ≈ 𝟙.*)
(*Proof.*)
(*  intros * In.*)
(*  destruct e1, e2.*)
(*  - generalize (MPComp_zero_left 𝟘).*)
(*    intros Eq.*)
(*    inversion Eq.*)
(*    generalize (MPInclusion_trans _ _ _ H0 In).*)
(*    intros Contra.*)
(*    unfold "⊑" in *.*)
(*    rewrite Eq in In.*)
(*    Search (𝟘 ⊙ _).*)

(*Lemma syxve : forall e, ~ e ⊑ 𝟘 -> exists m, m ∈ e.*)
(*Proof.*)
(*  induction e; intros Not;*)
(*  try (eexists; now constructor).*)
(*  - exfalso; now apply Not.*)
(*  - eexists.*)
(*    constructor.*)
(**)
(*    assert (~ e1 ⊑ 𝟘 \/ ~ e2 ⊑ 𝟘).*)
(*    {*)
(*      constructor.*)
(*      - intros Inc.*)
(*        apply Not.*)
(*        intros m mIn.*)
(*        inversion mIn; subst.*)
(*        + apply MPInclusion_zero in Inc.*)
(*          now rewrite <- Inc.*)
(*        +*)
(*      +*)
(*      Search (_ ⊑ 𝟘).*)
(*    }*)
(*  - eexists; constructor.*)
(**)
(**)
(*Lemma asdvxes : forall e1 e2 m,*)
(*  e1 ⊙ e2 ⊑ 𝟙 ->*)
(*  ~ e1 ⊑ 𝟘 ->*)
(*  ~ e2 ⊑ 𝟘 ->*)
(*  m ∈ e1 ->*)
(*  m ∈ 𝟙.*)
(*Proof.*)
(*  induction e1; intros * Inc Note1 Note2 In;*)
(*  try (inversion In; fail);*)
(*  try assumption.*)
(*  - *)
(**)
(**)
(*  induction e1, e2; intros * Inc Note1 Note2 In;*)
(*  try (inversion In; fail);*)
(*  try assumption.*)
(*  - inversion In; subst.*)
(*    generalize (MPComp_zero_left « m »).*)
(*    intros [Inc1 Inc2].*)
(*    exfalso.*)
(*    apply Note2.*)
(*    apply reflexivity.*)
(*  - generalize (MPComp_unit « m »).*)
(*    intros Eq.*)
(*    unfold "⊑" in Inc.*)
(*    setoid_rewrite Eq in Inc.*)
(*    now apply Inc.*)
(*  - inversion In; subst.*)
(*    unfold "⊑" in Inc.*)
(*    assert ((⟨ m ⟩ ⊎ ⟨ m0 ⟩) ∈ « m » ⊙ « m0 ») by (eapply MPValueComp; now constructor).*)
(*    generalize (Inc _ H).*)
(*    intros Contra; inversion Contra.*)
(*  -*)
(**)
(*Lemma sadfegwef : forall e1 e2 f,*)
(*  ~ f ⊑ 𝟘 ->*)
(*  ~ e1 ⊑ 𝟘 ->*)
(*  ~ e2 ⊑ 𝟘 ->*)
(*  e1 ⊙ e2 ⊑ f ->*)
(*  exists f1 f2, f ≈ f1 ⊙ f2 /\ e1 ⊑ f1 /\ e2 ⊑ f2.*)
(*Proof.*)
(*  intros * Notf Note1 Note2 In.*)
(*  destruct f.*)
(*  - exfalso.*)
(*    apply Notf.*)
(*    apply MPInclusion_zero.*)
(*    intros m mIn.*)
(*    inversion mIn.*)
(*  - exists 𝟙, 𝟙; repeat split; intros m mIn.*)
(*    + eapply MPValueComp; try constructor. simpl. now inversion mIn.*)
(*    + inversion mIn; subst; inversion H1; inversion H3; subst; simpl in *.*)
(*      now rewrite H4.*)
(*    + admit.*)
(*    + *)
(*    Search (_ ≈ 𝟙).*)
(**)
(*Lemma sdfasef : forall T T1 T2 U U1 U2,*)
(*  U1 ▷ U2 ~= U ->*)
(*  T1 ≤ U ->*)
(*  T1 ▷ T2 ~= T ->*)
(*  exists U1' U2' T2' A1 A2,*)
(*    U2' ▷ T2' ~= A2 /\*)
(*    U1' ▷ A2 ~= A1 /\*)
(*    T ≤ A1 /\*)
(*    U1' ≤ U1 /\*)
(*    U2' ≤ U2 /\*)
(*    T2' ≤ T2.*)
(*Proof.*)
(*  intros * Comb1 Sub Comb2.*)
(*  revert T1 T2 T Comb2 Sub.*)
(*  induction Comb1; intros; inversion Comb2; subst.*)
(*  - inversion Sub; subst.*)
(*    repeat exists (TUBase c); repeat constructor.*)
(*  - inversion Sub; subst.*)
(*  - inversion Sub; subst.*)
(*  - inversion H1; subst.*)
(*    + inversion Sub; subst.*)
(*      * inversion H0; subst; inversion H2; subst.*)
(*        -- inversion H; subst.*)
(*           ++ Search (_ ⊙ _ ⊑ _).*)

End mailbox_types_properties.
