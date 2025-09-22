(** * Typing environments *)

From MailboxTypes Require Export Types.
From MailboxTypes Require Import Util.
From MailboxTypes Require Export Dblib.Environments.

From Stdlib Require Export Lists.List.
Export ListNotations.
From Stdlib Require Import Lia.

Generalizable All Variables.

Create HintDb environment.

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

  Definition Env := env TUsage.

  (** Definition 3.4 of environment subtyping.
      Subtyping of environments includes weakening for unrestricted types.
      This representation relates two environments of equal length, but
      they may contain different amounts of types
  *)
  Inductive EnvironmentSubtype : Env -> Env -> Prop :=
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
        EnvironmentSubtype (Some T1 :: env1) (Some T2 :: env2)
    | EnvSubtypeTrans : forall env1 env2 env3,
        EnvironmentSubtype env1 env2 ->
        EnvironmentSubtype env2 env3 ->
        EnvironmentSubtype env1 env3
    | EnvSubtypeRefl : forall env, EnvironmentSubtype env env.

  (** Strict environment subtyping.
      Strict subtyping of environments is same as normal
      subtyping but the domains of both environments must be
      equal. In our representation this means that for every
      index in every list, both contain either None or Some.
  *)
  Inductive EnvironmentSubtypeStrict : Env -> Env -> Prop :=
    | EnvSubtypeStrNone : forall env1 env2,
        EnvironmentSubtypeStrict env1 env2 ->
        EnvironmentSubtypeStrict (None :: env1) (None :: env2)
    | EnvSubtypeStrSub : forall env1 env2 T1 T2,
        Subtype T1 T2 ->
        EnvironmentSubtypeStrict env1 env2 ->
        EnvironmentSubtypeStrict (Some T1 :: env1) (Some T2 :: env2)
    | EnvSubtypeStrTrans : forall env1 env2 env3,
        EnvironmentSubtypeStrict env1 env2 ->
        EnvironmentSubtypeStrict env2 env3 ->
        EnvironmentSubtypeStrict env1 env3
    | EnvSubtypeStrRefl : forall env, EnvironmentSubtypeStrict env env.

  (** Definition 3.8 of environment combination.
      This representation relates three environments of equal length, but
      they may contain different amounts of types
  *)
  Inductive EnvironmentCombination : Env -> Env -> Env -> Prop :=
      EnvCombEmpty : EnvironmentCombination nil nil nil
    (* Special constructor for our representation of environments *)
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

  Definition UnrestrictedEnv : Env -> Prop :=
    ForallMaybe Unrestricted.

  (** An empty environment contains only None as entries *)
  Definition EmptyEnv (e : Env) : Prop := Forall (fun x => x = None) e.

  (** A singleton environment contains only a single type *)
  Fixpoint SingletonEnv (e : Env) (T : TUsage) : Prop :=
    match e with
    | nil => False
    | None :: e' => SingletonEnv e' T
    | (Some T') :: e' => if TUsage_eq_dec T T' then EmptyEnv e' else False
    end.

  (** Creates an empty environment based on the size of the provided environment *)
  Fixpoint create_EmptyEnv (e : Env) : Env :=
    match e with
    | nil => nil
    | t :: e' => None :: create_EmptyEnv e'
    end.

End environment_def.

Hint Resolve EnvSubtypeNone : environment.
Hint Resolve EnvSubtypeUn : environment.
Hint Resolve EnvSubtypeSub : environment.
Hint Resolve EnvSubtypeRefl : environment.
Hint Resolve EnvSubtypeStrNone : environment.
Hint Resolve EnvSubtypeStrSub : environment.
Hint Immediate EnvSubtypeStrRefl : environment.
Hint Constructors EnvironmentCombination : environment.
Hint Constructors EnvironmentDisjointCombination : environment.
Hint Constructors EnvironmentDisjointCombinationN : environment.

(** Notation for environments *)
Declare Scope environment_scope.
Open Scope environment_scope.

Notation "Env1 ≤ₑ Env2" := (EnvironmentSubtype Env1 Env2) (at level 80) : environment_scope.
Notation "Env1 ≼ₑ Env2" := (EnvironmentSubtypeStrict Env1 Env2) (at level 80) : environment_scope.
Notation "Env1 ▷ₑ Env2 ~= Env" := (EnvironmentCombination Env1 Env2 Env) (at level 80) : environment_scope.
Notation "Env1 +ₑ Env2 ~= Env" := (EnvironmentDisjointCombination Env1 Env2 Env) (at level 80) : environment_scope.
(* TODO: Change the below notation. It sometimes collides with list notations *)
Notation "[ Env1 ]+ₑ ~= Env" := (EnvironmentDisjointCombinationN Env1 Env) (at level 0) : environment_scope.
Notation "⌊ Env ⌋ₑ" := (returnEnvironment Env) (at level 0) : environment_scope.
Notation "⌈ Env ⌉ₑ" := (secondEnvironment Env) (at level 0) : environment_scope.

(** ** Properties of environments *)
Section environment_properties.

  Context `{M : IMessage Message}.

  Lemma CruftEnv_EnvironmentSubtype_Empty : forall env,
    CruftEnv env ->
    exists env', EmptyEnv env' /\ env ≤ₑ env'.
  Proof.
    induction env; intros CruftE.
    - exists []; split; repeat constructor.
    - inversion CruftE; subst.
      generalize (IHenv H2).
      intros [env' [Empty Sub]].
      exists (None :: env'); split.
      + now constructor.
      + destruct a; try destruct t; try destruct u.
        * repeat constructor; assumption.
        * simpl in H1.
          unfold Irrelevant in H1.
          generalize (H1 SecondClass); intros Sub'.
          eapply EnvSubtypeTrans with (env2 := Some (! 𝟙 ^^ ◦) :: env').
          now constructor.
          repeat constructor.
        * easy.
        * now constructor.
  Qed.

  Lemma EmptyEnv_implies_CruftEnv : forall env, EmptyEnv env -> CruftEnv env.
  Proof.
    induction env; intros Empty.
    - constructor.
    - inversion Empty; subst.
      constructor.
      apply I.
      now apply IHenv.
  Qed.

  Lemma secondEnvironment_idem : forall env, ⌈ env ⌉ₑ = ⌈ ⌈ env ⌉ₑ ⌉ₑ.
  Proof.
    induction env.
    - easy.
    - simpl. destruct a.
      + simpl.
        rewrite <- secondUsage_idem.
        now f_equal.
      + simpl. now f_equal.
  Qed.

  Lemma EmptyEnv_lookup : forall env, EmptyEnv env -> (forall x, lookup x env = None).
  Proof.
    induction env; simpl.
    - intros Empty x; now destruct x.
    - intros Empty x.
      inversion Empty; subst.
      destruct x; simpl.
      + easy.
      + rewrite lookup_successor; now apply IHenv.
  Qed.

  Lemma lookup_nil : forall {A} x, @lookup A x [] = None.
  Proof.
    now destruct x.
  Qed.

  Lemma EnvironmentCombination_length : forall env1 env2 env3,
    env1 ▷ₑ env2 ~= env3 ->
    length env1 = length env3 /\ length env2 = length env3.
  Proof.
    intros * Comb.
    induction Comb;
    try (simpl; destruct IHComb as [IH1 IH2]; split; f_equal);
    auto.
  Qed.

  Lemma EnvironmentDis_length : forall env1 env2 env3,
    env1 +ₑ env2 ~= env3 ->
    length env1 = length env3 /\ length env2 = length env3.
  Proof.
    intros * Comb.
    induction Comb;
    try (simpl; destruct IHComb as [IH1 IH2]; split; f_equal);
    auto.
  Qed.

  Lemma create_EmptyEnv_EmptyEnv : forall env, EmptyEnv (create_EmptyEnv env).
  Proof.
    induction env.
    - constructor.
    - now constructor.
  Qed.

  Lemma EnvironmentSubtype_length : forall env1 env2, env1 ≤ₑ env2 -> length env1 = length env2.
  Proof.
    intros * Sub.
    induction Sub; simpl;
    try (f_equal; try easy; fail).
    rewrite IHSub1; now rewrite IHSub2.
  Qed.

  Lemma create_EmptyEnv_length : forall env1 env2,
    length env1 = length env2 ->
    create_EmptyEnv env1 = create_EmptyEnv env2.
  Proof.
    induction env1, env2; intros Eq;
    try discriminate Eq.
    - easy.
    - simpl in *; f_equal; apply IHenv1; eauto.
  Qed.

  Lemma create_EmptyEnv_length_same : forall env,
    length env = length (create_EmptyEnv env).
  Proof.
    induction env; simpl; auto.
  Qed.

  Lemma EnvironmentSubtype_create_EmptyEnv : forall env1 env2,
    env1 ≤ₑ env2 ->
    create_EmptyEnv env1 ≤ₑ create_EmptyEnv env2.
  Proof.
    intros.
    apply EnvironmentSubtype_length in H.
    apply create_EmptyEnv_length in H.
    rewrite H; constructor.
  Qed.

  Lemma EmptyEnv_SubEnv_EmptyEnv : forall env1 env2,
    EmptyEnv env1 -> env1 ≤ₑ env2 -> EmptyEnv env2.
  Proof.
    intros * Empty Sub; induction Sub; inversion Empty; subst;
    try eauto; try discriminate.
    constructor; try reflexivity; now apply IHSub.
  Qed.

  Lemma UnrestrictedEnv_EmptyEnv : forall env, EmptyEnv env -> UnrestrictedEnv env.
  Proof.
    induction env.
    - constructor.
    - intros Empty.
      inversion Empty; subst; constructor.
      + easy.
      + now apply IHenv.
  Qed.

  Lemma SubEnv_EmptyEnv_create_EmptyEnv : forall env,
    EmptyEnv env ->
    env ≤ₑ create_EmptyEnv env.
  Proof.
    intros * Empty; induction env; simpl in *;
    inversion Empty; subst; eauto with environment.
  Qed.

  (* This has to be here for now *)
  Hint Resolve SubEnv_EmptyEnv_create_EmptyEnv : environment.

  Lemma EnvironmentSubtypeStrict_refl : forall env, env ≼ₑ env.
  Proof.
    induction env; eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_refl : forall env, env ≤ₑ env.
  Proof.
    induction env; eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_trans : forall env1 env2 env3, env1 ≤ₑ env2 -> env2 ≤ₑ env3 -> env1 ≤ₑ env3.
  Proof.
    apply EnvSubtypeTrans.
  Qed.

  Lemma EnvironmentDis_implies_Comb : forall env1 env2 env, env1 +ₑ env2 ~= env -> env1 ▷ₑ env2 ~= env.
  Proof.
    intros * Dis; induction Dis; now repeat constructor.
  Qed.

  Lemma EnvironmentDis_Comb_comm : forall env1 env2 env,
    env1 +ₑ env2 ~= env -> env2 +ₑ env1 ~= env.
  Proof.
    intros * Dis.
    induction Dis; eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_None_inv : forall env1 env2,
    None :: env1 ≤ₑ env2 ->
    exists env2',
    env2 = None :: env2' /\ env1 ≤ₑ env2'.
  Proof.
    intros * Sub.
    remember (None :: env1) as E.
    revert env1 HeqE.
    induction Sub; intros; subst; try discriminate.
    - inversion HeqE; subst; now exists env2.
    - generalize (IHSub1 env0 eq_refl).
      intros [env1' [Eq1' Sub1']].
      generalize (IHSub2 env1' Eq1').
      intros [env2' [Eq2' Sub2']].
      exists env2'.
      + constructor.
        assumption.
        eapply EnvSubtypeTrans; eassumption.
    - exists env1; constructor.
      reflexivity.
      apply EnvironmentSubtype_refl.
  Qed.

  Lemma EnvironmentSubtype_None_None_inv : forall env1 env2,
    None :: env1 ≤ₑ None :: env2 ->
    env1 ≤ₑ env2.
  Proof.
    intros * Sub.
    remember (None :: env1) as E1.
    remember (None :: env2) as E2.
    revert env1 env2 HeqE1 HeqE2.
    induction Sub; intros; subst; try discriminate.
    - inversion HeqE1; inversion HeqE2; now subst.
    - apply EnvironmentSubtype_None_inv in Sub1.
      destruct Sub1 as [env2' [Eq' Sub']].
      generalize (IHSub2 env2' env4 Eq' eq_refl).
      generalize (IHSub1 env0 env2' eq_refl Eq').
      intros Sub1' Sub2'.
      eapply EnvSubtypeTrans; eassumption.
    - inversion HeqE2; subst. apply EnvironmentSubtype_refl.
  Qed.

  Lemma EnvironmentSubtype_nil_right : forall env, env ≤ₑ [] -> env = [].
  Proof.
    intros * Sub; remember [] as E; revert HeqE.
    induction Sub; intros; subst; try easy.
    rewrite IHSub2 in * by reflexivity; now apply IHSub1.
  Qed.

  Lemma EnvironmentSubtype_nil_left : forall env, [] ≤ₑ env -> env = [].
  Proof.
    intros * Sub; remember [] as E; revert HeqE.
    induction Sub; intros; subst; try easy.
    rewrite IHSub1 in * by reflexivity; now apply IHSub2.
  Qed.

  Lemma EnvironmentSubtype_Some_nil : forall env A, ~ (Some A :: env ≤ₑ []).
  Proof.
    intros * Sub.
    remember (Some A :: env) as E.
    remember [] as E'.
    revert A env HeqE HeqE'.
    induction Sub; intros; subst; try discriminate.
    eapply IHSub1. reflexivity. now apply EnvironmentSubtype_nil_right.
  Qed.

  Lemma EnvironmentSubtype_cons_nil : forall env e, ~ (e :: env ≤ₑ []).
  Proof.
    intros * Sub.
    remember (e :: env) as E.
    remember [] as E'.
    revert e env HeqE HeqE'.
    induction Sub; intros; subst; try discriminate.
    eapply IHSub1. reflexivity. now apply EnvironmentSubtype_nil_right.
  Qed.

  Lemma EnvironmentSubtype_None_Some : forall env1 env2 T,
    ~ (None :: env1 ≤ₑ Some T :: env2).
  Proof.
    intros * WT.
    remember (None :: env1) as E1.
    remember (Some T :: env2) as E2.
    revert env1 env2 T HeqE1 HeqE2.
    induction WT; intros; subst; try discriminate.
    destruct env2.
    - now apply EnvironmentSubtype_nil_right in WT1.
    - destruct o.
      + eapply IHWT1; reflexivity.
      + eapply IHWT2; reflexivity.
  Qed.

  Lemma EnvironmentSubtype_Some_Some_inv : forall env1 env2 T1 T2,
    Some T1 :: env1 ≤ₑ Some T2 :: env2 ->
    T1 ≤ T2 /\ env1 ≤ₑ env2.
  Proof.
    intros * Sub.
    remember (Some T1 :: env1) as E1.
    remember (Some T2 :: env2) as E2.
    revert env1 env2 T1 T2 HeqE1 HeqE2.
    induction Sub; intros; subst; try discriminate.
    - inversion HeqE1; inversion HeqE2; now subst.
    - destruct env2.
      + now apply EnvironmentSubtype_nil_right in Sub1.
      + destruct o.
        * generalize (IHSub1 env0 env2 T1 t eq_refl eq_refl).
            generalize (IHSub2 env2 env4 t T2 eq_refl eq_refl).
            intros [Sub1' EnvSub1'][Sub2' EnvSub2'].
            constructor.
            -- eapply Subtype_trans; eassumption.
            -- eapply EnvSubtypeTrans; eassumption.
        * now apply EnvironmentSubtype_None_Some in Sub2.
    - inversion HeqE2; constructor.
      apply Subtype_refl.
      apply EnvironmentSubtype_refl.
  Qed.

  Lemma EnvironmentSubtype_Some_None_inv : forall env1 env2 T,
    Some T :: env1 ≤ₑ None :: env2 ->
    exists T',
    Unrestricted T' /\ T ≤ T' /\ env1 ≤ₑ env2.
  Proof.
    intros * Sub.
    remember (Some T :: env1) as E1.
    remember (None :: env2) as E2.
    revert env1 env2 T HeqE1 HeqE2.
    induction Sub; intros; subst; try discriminate.
    - inversion HeqE1; inversion HeqE2; subst.
      exists T0; repeat constructor; try assumption.
      apply Subtype_refl.
    - destruct env2.
      + now apply EnvironmentSubtype_nil_right in Sub1.
      + destruct o.
        * generalize (IHSub2 _ _ t eq_refl eq_refl).
          intros [T' [Unr' [Sub' EnvSub']]].
          apply EnvironmentSubtype_Some_Some_inv in Sub1.
          destruct Sub1 as [Sub'' EnvSub''].
          exists T'; repeat constructor.
          -- assumption.
          -- eapply Subtype_trans; eassumption.
          -- eapply EnvSubtypeTrans; eassumption.
        * generalize (IHSub1 _ _ T eq_refl eq_refl).
          intros [T' [Unr' [Sub' EnvSub']]].
          apply EnvironmentSubtype_None_None_inv in Sub2.
          exists T'; repeat constructor; try assumption.
          eapply EnvSubtypeTrans; eassumption.
  Qed.

  Lemma EnvironmentSubtype_Some_inv : forall env1 env2 T,
    Some T :: env1 ≤ₑ env2 ->
    exists env2',
    (env2 = None :: env2' /\ env1 ≤ₑ env2') \/
    exists T', (env2 = Some T' :: env2' /\ T ≤ T' /\ env1 ≤ₑ env2').
  Proof.
    intros * Sub.
    destruct env2.
    - now apply EnvironmentSubtype_nil_right in Sub.
    - destruct o as [T' |].
      + apply EnvironmentSubtype_Some_Some_inv in Sub.
        destruct Sub as [Sub EnvSub].
        exists env2; right. now exists T'.
      + apply EnvironmentSubtype_Some_None_inv in Sub.
        destruct Sub as [T' [Unr [Sub EnvSub]]].
        now exists env2; left.
  Qed.

  Lemma EnvironmentSubtype_Some_inv' : forall env1 env2 T,
    Some T :: env1 ≤ₑ env2 ->
    exists env2' T',
    T ≤ T' /\ env1 ≤ₑ env2' /\
    ((env2 = None :: env2' /\ Unrestricted T') \/
    (env2 = Some T' :: env2')).
  Proof.
    intros * Sub; destruct env2.
    - now apply EnvironmentSubtype_nil_right in Sub.
    - destruct o as [T' |].
      + apply EnvironmentSubtype_Some_Some_inv in Sub.
        destruct Sub as [Sub EnvSub].
        exists env2, T'; repeat split; try assumption.
        now right.
      + apply EnvironmentSubtype_Some_None_inv in Sub.
        destruct Sub as [T' [Unr [Sub EnvSub]]].
        exists env2, T'; repeat split; try assumption.
        now left.
    Qed.

  Lemma EnvironmentSubtype_nil_insert_right : forall env x T, ~ ([] ≤ₑ insert x T env).
  Proof.
    induction x; intros * Sub;
    (rewrite raw_insert_zero in Sub || rewrite raw_insert_successor in Sub);
    now apply EnvironmentSubtype_nil_left in Sub.
  Qed.

  Lemma EnvironmentSubtype_nil_insert_left : forall env x T, ~ (insert x T env ≤ₑ []).
  Proof.
    induction x; intros * Sub;
    (rewrite raw_insert_zero in Sub || rewrite raw_insert_successor in Sub).
    - now apply EnvironmentSubtype_Some_nil in Sub.
    - now apply EnvironmentSubtype_cons_nil in Sub.
  Qed.

  Lemma lookup_zero : forall {A} env (e : option A),
    lookup 0 (e :: env) = e.
  Proof. reflexivity. Qed.

  Lemma lookup_successor_cons : forall {A} x env (e : option A),
    lookup (S x) (e :: env) = lookup x env.
  Proof. reflexivity. Qed.

  Lemma insert_EmptyEnv : forall env T x,
    ~ EmptyEnv (insert x T env).
  Proof.
    intros * Empty.
    remember (insert x T env) as I.
    revert x T env HeqI.
    induction Empty; intros y * Insert.
    - eauto using insert_nil.
    - subst.
      destruct y.
      + discriminate.
      + rewrite raw_insert_successor in Insert.
        inversion Insert; eapply IHEmpty; eassumption.
  Qed.

  Lemma BaseEnv_raw_insert_None_inv : forall x env,
    BaseEnv (raw_insert x None env) ->
    BaseEnv env.
  Proof.
    induction x; intros * Base.
    - now rewrite raw_insert_zero in Base.
    - destruct env.
      + constructor.
      + rewrite raw_insert_successor in Base.
        rewrite lookup_zero in Base.
        destruct o; simpl in *; try destruct t; eauto.
    Qed.

  Ltac simpl_SubEnv :=
    match goal with
    | H : context [None :: ?env1 ≤ₑ ?env2 ] |- _ =>
        apply EnvironmentSubtype_None_inv in H;
        let env2' := fresh "env2'" in
        let Eq := fresh "Eq" in
        let Sub := fresh "Sub" in
        destruct H as [env2' [Eq Sub]]; subst
    | H : context [Some _ :: ?env1 ≤ₑ ?env2 ] |- _ =>
        apply EnvironmentSubtype_Some_inv' in H;
        let env2' := fresh "env2" in
        let Eq := fresh "Eq" in
        let EnvSub := fresh "EnvSub" in
        let T := fresh "T" in
        let Sub := fresh "Sub" in
        let Unr := fresh "Unr" in
        destruct H as [env2' [T [Sub [EnvSub [[Eq Unr] | Eq]]]]]
    | H : ?env ≤ₑ [] |- _ =>
        now apply EnvironmentSubtype_nil_right in H
    | H : context [Some _ :: ?env1 ≤ₑ Some _ :: ?env2 ] |- _ =>
        apply EnvironmentSubtype_Some_Some_inv in H;
        let EnvSub := fresh "EnvSub" in
        let Sub := fresh "Sub" in
        destruct H as [Sub EnvSub]
    end.

  Lemma EnvironmentSubtype_insert_right_inv : forall x T env1 env2,
    env1 ≤ₑ insert x T env2 ->
    exists env1' T', T' ≤ T /\ env1 = insert x T' env1'.
  Proof.
    induction x; intros * Sub.
    - rewrite raw_insert_zero in *.
      destruct env1.
      apply EnvironmentSubtype_nil_left in Sub. discriminate.
      destruct o.
      + simpl_SubEnv.
        discriminate.
        inversion Eq; subst.
        exists env1, t.
        now rewrite raw_insert_zero.
      + simpl_SubEnv; discriminate.
    - rewrite raw_insert_successor in Sub.
      destruct env2.
      + rewrite lookup_nil in Sub; simpl in *.
        destruct env1.
        apply EnvironmentSubtype_nil_left in Sub. discriminate.
        destruct o; simpl_SubEnv; inversion Eq; subst.
        * apply IHx in EnvSub.
          destruct EnvSub as [env1' [T' [Sub' Eq']]]; subst.
          exists (Some t :: env1'), T'.
          rewrite raw_insert_successor.
          now rewrite lookup_zero.
        * apply IHx in Sub0.
          destruct Sub0 as [env1' [T' [Sub' Eq']]]; subst.
          exists (None :: env1'), T'.
          rewrite raw_insert_successor.
          now rewrite lookup_zero.
      + rewrite lookup_zero in Sub; simpl in *.
        destruct env1.
        * apply EnvironmentSubtype_nil_left in Sub; discriminate.
        * destruct o0, o; simpl_SubEnv; inversion Eq; subst.
          -- apply IHx in EnvSub.
             destruct EnvSub as [env1' [T' [Sub' Eq']]]; subst.
             exists (Some t :: env1'), T'.
             rewrite raw_insert_successor.
             now rewrite lookup_zero.
          -- apply IHx in EnvSub.
             destruct EnvSub as [env1' [T' [Sub' Eq']]]; subst.
             exists (Some t :: env1'), T'.
             rewrite raw_insert_successor.
             now rewrite lookup_zero.
          -- apply IHx in Sub0.
             destruct Sub0 as [env1' [T' [Sub' Eq']]]; subst.
             exists (None :: env1'), T'.
             rewrite raw_insert_successor.
             now rewrite lookup_zero.
  Qed.

  Lemma EnvironmentSubtype_insert_inv : forall env1 env2 x T,
    insert x T env1 ≤ₑ env2 ->
    exists env2' T',
    T ≤ T' /\ env1 ≤ₑ env2' /\
    ((env2 = raw_insert x None env2' /\ Unrestricted T') \/
    (env2 = insert x T' env2')).
  Proof.
    intros until x.
    revert env1 env2.
    induction x; intros * Sub.
    - rewrite raw_insert_zero in Sub.
      apply EnvironmentSubtype_Some_inv' in Sub;
      destruct Sub as [env2' [T' [Sub [EnvSub [[Eq Unr] | Eq]]]]];
      subst; exists env2', T'; eauto.
    - rewrite raw_insert_successor in Sub.
      destruct env1.
      + rewrite lookup_nil in Sub; simpl in *.
        apply EnvironmentSubtype_None_inv in Sub.
        destruct Sub as [env' [Eq Sub]]; subst.
        generalize (IHx _ _ _ Sub).
        intros [env2' [T' [Sub' [EnvSub' [[Eq Un] | Eq]]]]].
        * generalize (EnvironmentSubtype_nil_left _ EnvSub').
          intros ->.
          exists [], T'; repeat split; try assumption.
          repeat rewrite raw_insert_successor; subst; simpl.
          rewrite lookup_nil; now left.
        * generalize (EnvironmentSubtype_nil_left _ EnvSub').
          intros ->.
          exists [], T'; repeat split; try assumption.
          repeat rewrite raw_insert_successor; subst; simpl.
          rewrite lookup_nil; now right.
      + rewrite lookup_zero in *; simpl in *.
        destruct o.
        * apply EnvironmentSubtype_Some_inv' in Sub;
          destruct Sub as [env2' [T' [Sub [EnvSub [[Eq Unr] | Eq]]]]]; subst.
          -- generalize (IHx _ _ _ EnvSub).
             intros [env2'' [T'' [Sub' [EnvSub' [[Eq Un] | Eq]]]]].
             ++ subst. exists (None :: env2''), T''.
                repeat rewrite raw_insert_successor;
                repeat rewrite lookup_zero; simpl; repeat split.
                assumption.
                eapply EnvironmentSubtype_trans with (env2 := Some T' :: env1);
                eauto with environment.
                now left.
             ++ subst. exists (None :: env2''), T''.
                repeat rewrite raw_insert_successor;
                repeat rewrite lookup_zero; simpl; repeat split.
                assumption.
                eapply EnvironmentSubtype_trans with (env2 := Some T' :: env1);
                eauto with environment.
                now right.
          -- generalize (IHx _ _ _ EnvSub).
             intros [env2'' [T'' [Sub' [EnvSub' [[Eq Un] | Eq]]]]];
             subst; exists (Some T' :: env2''), T'';
             repeat rewrite raw_insert_successor;
             repeat rewrite lookup_zero; simpl; repeat split; eauto;
             eapply EnvironmentSubtype_trans with (env2 := Some T' :: env2'');
             eauto with environment.
        * apply EnvironmentSubtype_None_inv in Sub;
          destruct Sub as [env' [Eq Sub']]; subst;
          generalize (IHx _ _ _ Sub');
          intros [env2'' [T'' [Sub'' [EnvSub' [[Eq Un] | Eq]]]]]; subst;
          exists (None :: env2''), T'';
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_zero; simpl; repeat split;
          eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_insert_extend : forall x T env1 env2,
    env1 ≤ₑ env2 ->
    insert x T env1 ≤ₑ insert x T env2.
  Proof.
    induction x; intros * Sub.
    - repeat rewrite raw_insert_zero.
      constructor; try apply Subtype_refl; assumption.
    - repeat rewrite raw_insert_successor.
      destruct env1, env2;
      repeat rewrite lookup_nil;
      repeat rewrite lookup_zero;
      simpl in *.
      + repeat constructor.
      + now apply EnvironmentSubtype_nil_left in Sub.
      + now apply EnvironmentSubtype_nil_right in Sub.
      + destruct o, o0.
        * apply EnvironmentSubtype_Some_Some_inv in Sub.
          destruct Sub as [? ?].
          eauto with environment.
        * apply EnvironmentSubtype_Some_None_inv in Sub.
          destruct Sub as [? [? [? ?]]].
          eauto using EnvSubtypeTrans with environment.
        * now apply EnvironmentSubtype_None_Some in Sub.
        * apply EnvironmentSubtype_None_None_inv in Sub.
          eauto with environment.
  Qed.

  Lemma EnvironmentCombination_tes : forall x T1 T2 env1 env2 env3,
    insert x T1 env1 ▷ₑ insert x T2 env2 ~= env3 ->
    exists env3' T,
      raw_insert x None env1 ▷ₑ raw_insert x None env2 ~= raw_insert x None env3' /\
      T1 ▷ T2 ~= T /\
      env3 = insert x T env3'.
  Proof.
    induction x; intros * Dis.
    - repeat rewrite raw_insert_zero in Dis.
      inversion Dis; subst.
      exists env, T.
      repeat rewrite raw_insert_zero; repeat split; eauto with environment.
    - repeat rewrite raw_insert_successor in Dis.
      destruct env1, env2;
      try rewrite lookup_nil in Dis;
      try rewrite lookup_zero in Dis;
      simpl in *.
      + inversion Dis; subst.
        generalize (IHx _ _ _ _ _ H1).
        intros [env3' [T [Dis' [Comb Eq]]]].
        subst.
        exists (None :: env3'), T.
        repeat rewrite raw_insert_successor.
        try rewrite lookup_nil;
        try rewrite lookup_zero;
        eauto with environment.
      + inversion Dis; subst.
        * generalize (IHx _ _ _ _ _ H3).
          intros [env3' [T [Dis' [Comb Eq]]]].
          subst.
          exists (None :: env3'), T.
          repeat rewrite raw_insert_successor;
          try rewrite lookup_nil;
          try rewrite lookup_zero;
          eauto with environment.
        * generalize (IHx _ _ _ _ _ H3).
          intros [env3' [T' [Dis' [Comb Eq]]]].
          subst.
          exists (Some T :: env3'), T'.
          repeat rewrite raw_insert_successor.
          repeat rewrite lookup_nil.
          repeat rewrite lookup_zero.
          simpl in *.
          eauto with environment.
      + inversion Dis; subst.
        * generalize (IHx _ _ _ _ _ H3).
          intros [env3' [T [Dis' [Comb Eq]]]].
          subst.
          exists (None :: env3'), T.
          repeat rewrite raw_insert_successor;
          try rewrite lookup_nil;
          try rewrite lookup_zero;
          eauto with environment.
        * generalize (IHx _ _ _ _ _ H3).
          intros [env3' [T' [Dis' [Comb Eq]]]].
          subst.
          exists (Some T :: env3'), T'.
          repeat rewrite raw_insert_successor.
          repeat rewrite lookup_nil.
          repeat rewrite lookup_zero.
          simpl in *.
          eauto with environment.
      + inversion Dis; subst; try rewrite lookup_zero in *; subst.
        * generalize (IHx _ _ _ _ _ H4).
          intros [env3' [T [Dis' [Comb Eq]]]].
          subst.
          exists (None :: env3'), T.
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_nil;
          repeat rewrite lookup_zero;
          simpl in *;
          eauto with environment.
        * generalize (IHx _ _ _ _ _ H4).
          intros [env3' [T' [Dis' [Comb Eq]]]].
          subst.
          exists (Some T :: env3'), T'.
          repeat rewrite raw_insert_successor.
          repeat rewrite lookup_nil.
          repeat rewrite lookup_zero.
          simpl in *.
          eauto with environment.
        * generalize (IHx _ _ _ _ _ H4).
          intros [env3' [T' [Dis' [Comb Eq]]]].
          subst.
          exists (Some T :: env3'), T'.
          repeat rewrite raw_insert_successor.
          repeat rewrite lookup_nil.
          repeat rewrite lookup_zero.
          simpl in *.
          eauto with environment.
        * generalize (IHx _ _ _ _ _ H4).
          intros [env3' [T' [Dis' [Comb Eq]]]].
          subst.
          exists (Some T :: env3'), T'.
          repeat rewrite raw_insert_successor.
          repeat rewrite lookup_nil.
          repeat rewrite lookup_zero.
          simpl in *.
          eauto with environment.
  Qed.

  Lemma insert_raw_insert_contra : forall {A} x (T : A) (env1 env2 : env A),
    ~ (insert x T env1 = raw_insert x None env2).
  Proof.
    intro.
    induction x; intros * Eq.
    - now repeat rewrite raw_insert_zero in Eq.
    - destruct env1, env2; repeat rewrite raw_insert_successor in Eq;
      try rewrite lookup_nil in Eq;
      try repeat rewrite lookup_zero in Eq;
      simpl in *; try (inversion Eq as [[e Eq']]; now apply IHx in Eq').
      inversion Eq as [Eq']; now apply IHx in Eq'.
  Qed.

  Lemma EnvironmentCombination_insert : forall x env1 env2 env T,
    env1 ▷ₑ env2 ~= insert x T env ->
    exists env1' env2',
      length env1' = length env /\ length env2' = length env /\ env1' ▷ₑ env2' ~= env /\
      ((env1 = insert x T env1' /\ env2 = raw_insert x None env2') \/
      (env1 = raw_insert x None env1' /\ env2 = insert x T env2') \/
      exists T1 T2, (env1 = insert x T1 env1' /\ env2 = insert x T2 env2' /\ T1 ▷ T2 ~= T)).
  Proof.
    induction x; intros * Comb.
    - rewrite raw_insert_zero in Comb.
      inversion Comb as [| | ? ? ? ? Comb' | ? ? ? ? Comb' | ? ? ? ? ? ? Comb' ].
      + generalize (EnvironmentCombination_length _ _ _ Comb'); subst.
        intros [L1 L2].
        exists env0, env3; repeat split; eauto.
      + generalize (EnvironmentCombination_length _ _ _ Comb'); subst.
        intros [L1 L2].
        exists env0, env3; repeat split; eauto.
      + generalize (EnvironmentCombination_length _ _ _ Comb'); subst.
        intros [L1 L2].
        exists env0, env3; repeat split; eauto.
        repeat right. setoid_rewrite raw_insert_zero; eauto.
    - destruct env; rewrite raw_insert_successor in Comb; simpl in *.
      + rewrite lookup_nil in Comb.
        inversion Comb; subst.
        * generalize (IHx _ _ _ _ H2).
          intros [env1' [env2' [L1 [L2 [Comb' [[Eq1 Eq2] | [[Eq1 Eq2] | [T1 [T2 [Eq1 [Eq2 TComb]]]]]]]]]]];
          inversion Comb'; subst; exists [], []; repeat split;
          try (repeat right; exists T1, T2); eauto using raw_insert_zero.
      + rewrite lookup_zero in Comb.
        destruct o;
        inversion Comb as [| | ? ? ? ? Comb' | ? ? ? ? Comb' | ? ? ? ? ? ? Comb' ]; subst.
        * generalize (IHx _ _ _ _ Comb').
          intros [env1' [env2' [L1 [L2 [Comb2 [[Eq1 Eq2] | [[Eq1 Eq2] | [T1 [T2 [Eq1 [Eq2 TComb]]]]]]]]]]];
          subst.
          -- exists (Some t :: env1'), (None :: env2'); repeat split; simpl;
             eauto using raw_insert_zero.
             now constructor.
          -- exists (Some t :: env1'), (None :: env2'); repeat split; simpl;
             eauto using raw_insert_zero.
             now constructor.
          -- generalize (IHx _ _ _ _ Comb').
             intros [env1'' [env2'' [L1' [L2' [Comb2' [[Eq1' Eq2'] | [[Eq1' Eq2'] | [T1' [T2' [Eq1' [Eq2' TComb']]]]]]]]]]];
             subst.
             ++ now apply insert_raw_insert_contra in Eq2'.
             ++ now apply insert_raw_insert_contra in Eq1'.
             ++ exists (Some t :: env1'), (None :: env2'); repeat split; simpl;
                eauto using raw_insert_zero.
                now constructor.
                repeat right; exists T1, T2; eauto.
        * generalize (IHx _ _ _ _ Comb').
          intros [env1' [env2' [L1 [L2 [Comb2 [[Eq1 Eq2] | [[Eq1 Eq2] | [T1 [T2 [Eq1 [Eq2 TComb]]]]]]]]]]];
          subst.
          -- exists (None :: env1'), (Some t :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (None :: env1'), (Some t :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (None :: env1'), (Some t :: env2'); repeat split; simpl; eauto.
             now constructor.
             repeat right; exists T1, T2;
             repeat rewrite raw_insert_successor;
             repeat rewrite lookup_zero; simpl; eauto.
        * generalize (IHx _ _ _ _ Comb').
          intros [env1' [env2' [L1 [L2 [Comb2 [[Eq1 Eq2] | [[Eq1 Eq2] | [T1' [T2' [Eq1 [Eq2 TComb]]]]]]]]]]];
          subst.
          -- exists (Some T1 :: env1'), (Some T2 :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (Some T1 :: env1'), (Some T2 :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (Some T1 :: env1'), (Some T2 :: env2'); repeat split; simpl; eauto.
             now constructor.
             repeat right; exists T1', T2';
             repeat rewrite raw_insert_successor;
             repeat rewrite lookup_zero; simpl; eauto.
        * generalize (IHx _ _ _ _ H).
          intros [env1' [env2' [L1 [L2 [Comb2 [[Eq1 Eq2] | [[Eq1 Eq2] | [T1' [T2' [Eq1 [Eq2 TComb]]]]]]]]]]];
          subst.
          -- exists (None :: env1'), (None :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (None :: env1'), (None :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (None :: env1'), (None :: env2'); repeat split; simpl; eauto.
             now constructor.
             repeat right; exists T1', T2'; eauto.
  Qed.

  Lemma EnvironmentSubtype_raw_insert_None : forall x env1 env2,
    raw_insert x None env1 ≤ₑ env2 ->
    exists env2', env2 = raw_insert x None env2' /\ env1 ≤ₑ env2'.
  Proof.
    induction x; intros * Sub.
    - rewrite raw_insert_zero in Sub.
      setoid_rewrite raw_insert_zero.
      now apply EnvironmentSubtype_None_inv in Sub.
    - destruct env1.
      + rewrite raw_insert_successor in Sub.
        setoid_rewrite raw_insert_successor.
        rewrite lookup_nil in Sub; simpl in *.
        apply EnvironmentSubtype_None_inv in Sub.
        destruct Sub as [env2' [Eq Sub]].
        apply IHx in Sub.
        destruct Sub as [env' [Eq' Sub']].
        exists (env').
        destruct env'; try rewrite lookup_nil; subst; simpl; eauto.
        apply EnvironmentSubtype_nil_left in Sub'; discriminate.
      + rewrite raw_insert_successor in Sub.
        rewrite lookup_zero in Sub; simpl in *.
        destruct o.
        * apply EnvironmentSubtype_Some_inv' in Sub.
          destruct Sub as [env2' [T' [Sub [EnvSub [[Eq Unr] | Eq]]]]]; subst;
          apply IHx in EnvSub;
          destruct EnvSub as [env' [Eq' EnvSub']].
          1: exists (None :: env').
          2: exists (Some T' :: env').
          all: subst; rewrite raw_insert_successor; rewrite lookup_zero;
               eauto using EnvironmentSubtype_trans with environment.
        * apply EnvironmentSubtype_None_inv in Sub.
          destruct Sub as [env2' [Eq EnvSub]].
          apply IHx in EnvSub;
          destruct EnvSub as [env' [Eq' EnvSub']].
          exists (None :: env').
          subst; rewrite raw_insert_successor; rewrite lookup_zero;
          eauto using EnvironmentSubtype_trans with environment.
  Qed.

  Lemma EmptyEnv_raw_insert_None : forall x env,
    EmptyEnv env <-> EmptyEnv (raw_insert x None env).
  Proof.
    induction x; intros *.
    - rewrite raw_insert_zero.
      split; intros H; now (constructor || inversion H).
    - rewrite raw_insert_successor.
      destruct env.
      + rewrite lookup_nil; simpl.
        split; intros H; constructor; try reflexivity; now rewrite IHx in H.
      + rewrite lookup_zero.
        split; intros H; inversion H; subst; simpl; constructor; try reflexivity.
        * now apply IHx in H3.
        * now apply IHx.
  Qed.

  Lemma raw_insert_None_over : forall {A} x (env : env A),
    length env <= x ->
    raw_insert x None env = env ++ repeat None (S (x - length env)).
  Proof.
    induction x; intros * L.
    - inversion L.
      apply length_zero_iff_nil in H0; subst.
      simpl; now setoid_rewrite raw_insert_zero.
    - destruct env as [| e env].
      + simpl in *; inversion L; subst.
        rewrite raw_insert_successor.
        rewrite lookup_nil.
        simpl.
        f_equal.
        generalize (IHx [] H0); simpl.
        now rewrite PeanoNat.Nat.sub_0_r.
      + simpl in *.
        apply le_S_n in L.
        apply IHx in L.
        rewrite raw_insert_successor.
        rewrite lookup_zero.
        simpl; now f_equal.
  Qed.

  (* TODO: Move to other file *)
  Lemma repeat_successor : forall {A} x,
    @repeat (option A) None (S x) = repeat None x ++ [None].
  Proof.
    intros; induction x; simpl in *; f_equal; eauto.
  Qed.

  Lemma EnvironmentCombination_app_last : forall (env1 env2 env : Env),
    env1 ▷ₑ env2 ~= env ++ [None] ->
    exists env1' env2',
      env1 = env1' ++ [None] /\
      env2 = env2' ++ [None] /\
      env1' ▷ₑ env2' ~= env.
  Proof.
    intros until env.
    revert env1 env2.
    induction env; intros * Comb.
    - simpl in *.
      inversion Comb; subst.
      inversion H2; subst.
      exists [], []; simpl; auto.
    - destruct a;
      inversion Comb as [| ? ? ? Comb' | ? ? ? ? Comb' | ? ? ? ? Comb' | ? ? ? ? T1 T2 Comb']; subst;
      apply IHenv in Comb';
      destruct Comb' as [env1' [env2' [Eq1 [Eq2 Comb']]]];
      subst.
        1: exists (Some t :: env1'), (None :: env2').
        2: exists (None :: env1'), (Some t :: env2').
        3: exists (Some T1 :: env1'), (Some T2 :: env2').
        4: exists (None :: env1'), (None :: env2').
        all: repeat split; now constructor.
  Qed.

  Lemma EnvironmentDis_app_last : forall (env1 env2 env : Env),
    env1 +ₑ env2 ~= env ++ [None] ->
    exists env1' env2',
      env1 = env1' ++ [None] /\
      env2 = env2' ++ [None] /\
      env1' +ₑ env2' ~= env.
  Proof.
    intros until env.
    revert env1 env2.
    induction env; intros * Dis.
    - simpl in *.
      inversion Dis; subst.
      inversion H2; subst.
      exists [], []; simpl; auto.
    - destruct a;
      inversion Dis as [| ? ? ? Dis' | ? ? ? ? Dis' | ? ? ? ? Dis' | ? ? ? ? Dis' ];
      apply IHenv in Dis';
      destruct Dis' as [env1' [env2' [Eq1 [Eq2 Dis']]]];
      subst.
        1: exists (Some t :: env1'), (None :: env2').
        2: exists (None :: env1'), (Some t :: env2').
        3: exists (Some (TUBase BT) :: env1'), (Some (TUBase BT) :: env2').
        4: exists (None :: env1'), (None :: env2').
        all: repeat split; now constructor.
  Qed.

  Lemma EnvironmentCombination_app : forall (env1 env2 env : Env) n,
    env1 ▷ₑ env2 ~= env ++ (repeat None n) ->
    exists env1' env2',
      env1 = env1' ++ repeat None n /\
      env2 = env2' ++ repeat None n /\
      env1' ▷ₑ env2' ~= env.
  Proof.
    intros until n.
    revert env1 env2 env.
    induction n; intros * Comb.
    - simpl in *.
      exists env1, env2.
      repeat rewrite app_nil_r in *; auto.
    - rewrite repeat_successor in Comb.
      rewrite app_assoc in Comb.
      apply EnvironmentCombination_app_last in Comb.
      destruct Comb as [env1' [env2' [Eq1 [Eq2 Comb']]]].
      apply IHn in Comb'.
      destruct Comb' as [env1'' [env2'' [Eq1' [Eq2' Comb']]]].
      subst; simpl in *.
      exists env1'', env2''.
      repeat rewrite <- app_assoc.
      rewrite repeat_cons; auto.
  Qed.

  Lemma EnvironmentDis_app : forall (env1 env2 env : Env) n,
    env1 +ₑ env2 ~= env ++ (repeat None n) ->
    exists env1' env2',
      env1 = env1' ++ repeat None n /\
      env2 = env2' ++ repeat None n /\
      env1' +ₑ env2' ~= env.
  Proof.
    intros until n.
    revert env1 env2 env.
    induction n; intros * Comb.
    - simpl in *.
      exists env1, env2.
      repeat rewrite app_nil_r in *; auto.
    - rewrite repeat_successor in Comb.
      rewrite app_assoc in Comb.
      apply EnvironmentDis_app_last in Comb.
      destruct Comb as [env1' [env2' [Eq1 [Eq2 Comb']]]].
      apply IHn in Comb'.
      destruct Comb' as [env1'' [env2'' [Eq1' [Eq2' Comb']]]].
      subst; simpl in *.
      exists env1'', env2''.
      repeat rewrite <- app_assoc.
      rewrite repeat_cons; auto.
  Qed.

  Lemma EnvironmentCombination_raw_insert_None : forall x env1 env2 env,
    env1 ▷ₑ env2 ~= raw_insert x None env ->
    exists env1' env2',
      (env1 = raw_insert x None env1' /\ length env1' = length env /\
       env2 = raw_insert x None env2' /\ length env2' = length env /\
       env1' ▷ₑ env2' ~= env).
  Proof.
    intros * Comb.
    destruct (Compare_dec.le_gt_dec (length env) x) as [Out | In].
    - generalize (raw_insert_None_over _ _ Out).
      intros Eq.
      rewrite Eq in Comb.
      apply EnvironmentCombination_app in Comb.
      destruct Comb as [env1' [env2' [Eq1 [Eq2 Comb]]]].
      subst.
      generalize (EnvironmentCombination_length _ _ _ Comb).
      intros [L1 L2].
      exists env1', env2'.
      simpl.
      assert (L1' : length env1' <= x) by lia.
      assert (L2' : length env2' <= x) by lia.
      apply raw_insert_None_over in L1'.
      apply raw_insert_None_over in L2'.
      rewrite L1'; rewrite L2'.
      rewrite L1; rewrite L2.
      auto.
    - generalize dependent env.
      revert env1 env2.
      induction x; intros.
      + rewrite raw_insert_zero in *.
        inversion Comb as [| env1' env2' ? Comb' | | |]; subst.
        exists env1', env2'.
        repeat rewrite raw_insert_zero.
        generalize (EnvironmentCombination_length _ _ _ Comb').
        intros [-> ->]; auto.
      + destruct env.
        inversion In.
        rewrite raw_insert_successor in Comb.
        rewrite lookup_zero in Comb.
        simpl in *.
        destruct o.
        * inversion Comb as [| | ? ? ? ? Comb' | ? ? ? ? Comb' | ? ? ? ? T1 T2 Comb']; subst;
          try apply IHx in Comb';
          try destruct Comb' as [env1' [env2' [Eq1 [L1 [Eq2 [L2 Comb']]]]]];
          subst;
          try lia.
          1 : exists (Some t :: env1'), (None :: env2').
          2 : exists (None :: env1'), (Some t :: env2').
          3 : exists (Some T1 :: env1'), (Some T2 :: env2').
          all : repeat rewrite raw_insert_successor;
                repeat rewrite lookup_zero;
                simpl; try rewrite L1, L2; repeat split; eauto with environment.
        * inversion Comb as [| ? ? ? Comb' | | | ]; subst.
          apply IHx in Comb';
          try destruct Comb' as [env1' [env2' [Eq1 [L1 [Eq2 [L2 Comb']]]]]];
          subst; try lia.
          exists (None :: env1'), (None :: env2').
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_zero;
          simpl; try rewrite L1, L2; repeat split; eauto with environment.
  Qed.

  Lemma EnvironmentCombination_raw_insert_Base : forall x c env1 env2 env,
    env1 ▷ₑ env2 ~= insert x (TUBase c) env ->
    exists env1' env2',
      env1' ▷ₑ env2' ~= env /\
      ((env1 = insert x (TUBase c) env1' /\ env2 = raw_insert x None env2') \/
       (env1 = raw_insert x None env1' /\ env2 = insert x (TUBase c) env2') \/
       (env1 = insert x (TUBase c) env1' /\ env2 = insert x (TUBase c) env2')).
  Proof.
    intros * Comb.
    generalize (EnvironmentCombination_insert x env1 env2 env _ Comb).
    intros [env1' [env2' [L1 [L2 [Comb' [[Eq1 Eq2] | [[Eq1 Eq2] | [T1 [T2 [Eq1 [Eq2 TComb]]]]]]]]]]];
    try (inversion TComb); subst; exists env1', env2'; eauto.
  Qed.

  Lemma EnvironmentDis_raw_insert_None : forall x env1 env2 env,
    env1 +ₑ env2 ~= raw_insert x None env ->
    exists env1' env2',
      (env1 = raw_insert x None env1' /\ length env1' = length env /\
       env2 = raw_insert x None env2' /\ length env2' = length env /\
       env1' +ₑ env2' ~= env).
  Proof.
    intros * Comb.
    destruct (Compare_dec.le_gt_dec (length env) x) as [Out | In].
    - generalize (raw_insert_None_over _ _ Out).
      intros Eq.
      rewrite Eq in Comb.
      apply EnvironmentDis_app in Comb.
      destruct Comb as [env1' [env2' [Eq1 [Eq2 Comb]]]].
      subst.
      generalize (EnvironmentDis_length _ _ _ Comb).
      intros [L1 L2].
      exists env1', env2'.
      simpl.
      assert (L1' : length env1' <= x) by lia.
      assert (L2' : length env2' <= x) by lia.
      apply raw_insert_None_over in L1'.
      apply raw_insert_None_over in L2'.
      rewrite L1'; rewrite L2'.
      rewrite L1; rewrite L2.
      auto.
    - generalize dependent env.
      revert env1 env2.
      induction x; intros.
      + rewrite raw_insert_zero in *.
        inversion Comb as [| env1' env2' ? Comb' | | |]; subst.
        exists env1', env2'.
        repeat rewrite raw_insert_zero.
        generalize (EnvironmentDis_length _ _ _ Comb').
        intros [-> ->]; auto.
      + destruct env.
        inversion In.
        rewrite raw_insert_successor in Comb.
        rewrite lookup_zero in Comb.
        simpl in *.
        destruct o;
        inversion Comb as [| ? ? ? Comb' | ? ? ? ? Comb' | ? ? ? ? Comb' | ? ? ? ? Comb' ];
        try apply IHx in Comb';
        try destruct Comb' as [env1' [env2' [Eq1 [L1 [Eq2 [L2 Comb']]]]]];
        subst;
        try lia.
        1 : exists (Some t :: env1'), (None :: env2').
        2 : exists (None :: env1'), (Some t :: env2').
        3 : exists (Some (TUBase BT) :: env1'), (Some (TUBase BT) :: env2').
        4 : exists (None :: env1'), (None :: env2').
        all : repeat rewrite raw_insert_successor;
              repeat rewrite lookup_zero;
              simpl; try rewrite L1, L2; repeat split; eauto with environment.
  Qed.

  Lemma EnvironmentDisCombination_insert : forall x env1 env2 env T,
    env1 +ₑ env2 ~= insert x T env ->
    exists env1' env2',
      length env1' = length env /\ length env2' = length env /\ env1' +ₑ env2' ~= env /\
      ((env1 = insert x T env1' /\ env2 = raw_insert x None env2') \/
      (env1 = raw_insert x None env1' /\ env2 = insert x T env2') \/
      exists BT, (env1 = insert x (TUBase BT) env1' /\ env2 = insert x (TUBase BT) env2')).
  Proof.
    induction x; intros * Dis.
    - rewrite raw_insert_zero in Dis.
      inversion Dis; subst.
      + generalize (EnvironmentDis_length _ _ _ H2).
        intros [L1 L2].
        exists env0, env3; repeat split; eauto.
      + generalize (EnvironmentDis_length _ _ _ H2).
        intros [L1 L2].
        exists env0, env3; repeat split; eauto.
      + generalize (EnvironmentDis_length _ _ _ H2).
        intros [L1 L2].
        exists env0, env3; repeat split; eauto.
        repeat right; exists BT. now repeat rewrite raw_insert_zero.
    - destruct env.
      + rewrite raw_insert_successor in Dis.
        rewrite lookup_nil in Dis; simpl in *.
        inversion Dis; subst.
        apply IHx in H2.
        destruct H2 as [env1' [env2' [L1 [L2 [Dis' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT [Eq1 Eq2]]]]]]]]].
        * subst; inversion Dis'; subst; exists [], []; repeat split; eauto.
        * subst; inversion Dis'; subst; exists [], []; repeat split; eauto.
        * subst; inversion Dis'; subst; exists [], []; repeat split; eauto.
          repeat right; exists BT; now repeat rewrite raw_insert_successor.
      + rewrite raw_insert_successor in Dis.
        rewrite lookup_zero in Dis.
        destruct o; simpl in *;
        inversion Dis as [| ? ? ? ? Dis' | ? ? ? ? Dis' | ? ? ? ? Dis' | ]; subst;
        try (apply IHx in Dis');
        try (destruct Dis' as [env1' [env2' [L1 [L2 [Dis' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT [Eq1 Eq2]]]]]]]]]);
        subst.
        * exists (Some t :: env1'), (None :: env2'); repeat split; simpl; eauto.
          now constructor.
        * exists (Some t :: env1'), (None :: env2'); repeat split; simpl; eauto.
          now constructor.
        * exists (Some t :: env1'), (None :: env2'); repeat split; simpl; eauto.
          now constructor.
          repeat right; exists BT; eauto.
        * exists (None :: env1'), (Some t :: env2'); repeat split; simpl; eauto.
          now constructor.
        * exists (None :: env1'), (Some t :: env2'); repeat split; simpl; eauto.
          now constructor.
        * exists (None :: env1'), (Some t :: env2'); repeat split; simpl; eauto.
          now constructor.
          repeat right; exists BT; eauto.
        * apply IHx in H.
          destruct H as [env1' [env2' [L1 [L2 [Dis' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT' [Eq1 Eq2]]]]]]]]];
          subst.
          -- exists (Some (TUBase BT) :: env1'), (Some (TUBase BT) :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (Some (TUBase BT) :: env1'), (Some (TUBase BT) :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (Some (TUBase BT) :: env1'), (Some (TUBase BT) :: env2'); repeat split; simpl; eauto.
             now constructor.
             repeat right; exists BT'; eauto.
        * apply IHx in H.
          destruct H as [env1' [env2' [L1 [L2 [Dis' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT' [Eq1 Eq2]]]]]]]]];
          subst.
          -- exists (None :: env1'), (None :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (None :: env1'), (None :: env2'); repeat split; simpl; eauto.
             now constructor.
          -- exists (None :: env1'), (None :: env2'); repeat split; simpl; eauto.
             now constructor.
             repeat right; exists BT'; eauto.
  Qed.

  Lemma EnvironmentDisCombination_insert_Type_eq : forall x T1 T2 env1 env2 env3,
    insert x T1 env1 +ₑ insert x T1 env2 ~= insert x T2 env3 ->
    T1 = T2.
  Proof.
    induction x; intros * Dis.
    - repeat rewrite raw_insert_zero in Dis.
      inversion Dis; now subst.
    - repeat rewrite raw_insert_successor in Dis.
      destruct env1, env2, env3;
      try (repeat rewrite lookup_nil in Dis);
      try (repeat rewrite lookup_zero in Dis);
      simpl in *;
      inversion Dis as [ Dis' | ? ? ? Dis' | ? ? ? ? Dis' | ? ? ? ? Dis' | ? ? ? ? Dis' ];
      try (inversion Dis; subst; now apply IHx in Dis').
  Qed.

  Lemma raw_insert_nil : forall [A : Type] (x : nat) (a : option A) (e : Environments.env A),
    raw_insert x a e = [] -> False.
  Proof.
    intros; destruct a.
    - now apply insert_nil in H.
    - destruct x.
      + rewrite raw_insert_zero in H; discriminate.
      + destruct e.
        * discriminate H.
        * rewrite raw_insert_successor in H;
          rewrite lookup_zero in H;
          discriminate.
  Qed.

  Lemma EnvironmentDis_Comb_raw_insert_None_all : forall x env1 env2 env,
    length env1 = length env ->
    length env2 = length env ->
    raw_insert x None env1 +ₑ raw_insert x None env2 ~= raw_insert x None env ->
    env1 +ₑ env2 ~= env.
  Proof.
    induction x; intros * L1 L2 Dis.
    - repeat rewrite raw_insert_zero in Dis;
      now inversion Dis.
    - repeat rewrite raw_insert_successor in Dis.
      destruct env1 as [| e1 env1'],
               env2 as [| e2 env2'],
               env as  [| e env'];
      try (inversion L1);
      try (inversion L2).
      + constructor.
      + simpl in *; repeat rewrite lookup_zero in Dis.
        inversion Dis; subst; constructor; now apply IHx.
  Qed.

  Lemma EnvironmentDis_Comb : forall env1 env2 env3 env2' env,
    env1 +ₑ env2' ~= env ->
    env2 ▷ₑ env3 ~= env2' ->
    exists env1', env1' ▷ₑ env3 ~= env /\ env1 +ₑ env2 ~= env1'.
  Proof.
    intros * Comb Dis.
    revert env1 env Comb.
    induction Dis; intros.
    - inversion Comb; subst; eauto with environment.
    - inversion Comb as [| ? ? ? Comb' | ? ? ? ? Comb' | |]; subst.
      + apply IHDis in Comb'.
        destruct Comb' as [env3' [Comb' Dis']].
        exists (None :: env3'); eauto with environment.
      + apply IHDis in Comb'.
        destruct Comb' as [env3' [Comb' Dis']].
        eauto with environment.
    - inversion Comb; subst.
      + apply IHDis in H3.
        destruct H3 as [env3' [Comb' Dis']].
        eauto with environment.
      + apply IHDis in H3.
        destruct H3 as [env3' [Comb' Dis']].
        eauto with environment.
    - inversion Comb; subst.
      + apply IHDis in H3.
        destruct H3 as [env3' [Comb' Dis']].
        eauto with environment.
      + apply IHDis in H3.
        destruct H3 as [env3' [Comb' Dis']].
        exists (Some (TUBase BT) :: env3'); split;
        repeat constructor; assumption.
    - inversion Comb; subst.
      + apply IHDis in H4.
        destruct H4 as [env3' [Comb' Dis']].
        eauto with environment.
      + apply IHDis in H4.
        destruct H4 as [env3' [Comb' Dis']].
        inversion H; subst.
        exists (Some (TUBase BT) :: env3'); split;
        repeat constructor; assumption.
  Qed.

  Lemma EnvironmentDis_Comb_rev : forall env1 env2 env3 env1' env,
    env1' +ₑ env3 ~= env ->
    env1 ▷ₑ env2 ~= env1' ->
    exists env2', env1 ▷ₑ env2' ~= env /\ env2 +ₑ env3 ~= env2'.
  Proof.
    intros * Dis1; revert env1 env2;
    induction Dis1; intros * Dis2; inversion Dis2; subst;
    try match goal with
    | H : ?env1 ▷ₑ ?env2 ~= ?env3 |- _ =>
      apply IHDis1 in H; destruct H as [env3' [Dis1' Dis2']]
    end;
    eauto with environment.
    - exists (Some (TUBase BT) :: env3'); now repeat constructor.
    - inversion H4; subst.
      exists (Some (TUBase BT) :: env3'); now repeat constructor.
  Qed.

  Lemma EnvironmentDis_assoc : forall env1 env2 env3 env2' env,
    env1 +ₑ env2' ~= env ->
    env2 +ₑ env3 ~= env2' ->
    exists env1', env1' +ₑ env3 ~= env /\ env1 +ₑ env2 ~= env1'.
  Proof.
    intros * Dis1; revert env2 env3;
    induction Dis1; intros * Dis2; inversion Dis2; subst;
    try match goal with
    | H : ?env1 +ₑ ?env2 ~= ?env3 |- _ =>
      apply IHDis1 in H; destruct H as [env3' [Dis1' Dis2']]
    end;
    eauto with environment.
  Qed.

  Lemma EnvironmentDis_assoc_rev : forall env1 env2 env3 env1' env,
    env1' +ₑ env2 ~= env ->
    env1 +ₑ env3 ~= env1' ->
    exists env2', env1 +ₑ env2' ~= env /\ env2 +ₑ env3 ~= env2'.
  Proof.
    intros * Dis1; revert env1 env3;
    induction Dis1; intros * Dis2; inversion Dis2; subst;
    try match goal with
    | H : ?env1 +ₑ ?env2 ~= ?env3 |- _ =>
      apply IHDis1 in H; destruct H as [env3' [Dis1' Dis2']]
    end;
    eauto with environment.
  Qed.

  Lemma EnvironmentCombination_assoc : forall env1 env2 env3 env2' env,
    env1 ▷ₑ env2' ~= env ->
    env2 ▷ₑ env3 ~= env2' ->
    exists env1', env1' ▷ₑ env3 ~= env /\ env1 ▷ₑ env2 ~= env1'.
  Proof.
    intros * Comb1; revert env2 env3.
    induction Comb1; intros * Comb2; inversion Comb2; subst;
    try match goal with
    | H : ?env1 ▷ₑ ?env2 ~= ?env3 |- _ =>
      apply IHComb1 in H; destruct H as [env3' [Comb1' Comb2']]
    end;
    eauto with environment.
    generalize (TypeUsageCombination_assoc _ _ _ _ _ H H5).
    intros [T' [Comb1'' Comb2'']].
    exists (Some T' :: env3'); split;
    eauto with environment.
  Qed.

  Lemma EnvironmentCombination_assoc_left : forall env1 env1' env2 env3 env,
    env1' ▷ₑ env2 ~= env ->
    env1 ▷ₑ env3 ~= env1' ->
    exists env2', env1 ▷ₑ env2' ~= env /\ env3 ▷ₑ env2 ~= env2'.
  Proof.
    intros * Comb1 Comb2.
    revert env2 env Comb1.
    induction Comb2; intros; inversion Comb1; subst;
    try (match goal with
    | H : ?env1 ▷ₑ ?env2 ~= ?env3 |- _ =>
      apply IHComb2 in H; destruct H as [env3' [Comb1' Comb2']]
    end); eauto with environment.
    - generalize (TypeUsageCombination_assoc_left _ _ _ _ _ H5 H).
      intros [T' [Comb1'' Comb2'']].
      exists (Some T' :: env3'); split;
      eauto with environment.
  Qed.

  Definition ReturnableEnv (env : Env) := ForallMaybe ReturnableType env.
  Definition SecondEnv (env : Env) := ForallMaybe SecondType env.

  Lemma EnvironmentSubtype_SecondEnv : forall env env',
    SecondEnv env ->
    env ≤ₑ env' ->
    SecondEnv env'.
  Proof.
    induction env; intros * S Sub.
    - apply EnvironmentSubtype_nil_left in Sub; now subst.
    - destruct a.
      + unfold SecondEnv in *.
        inversion S; subst.
        apply EnvironmentSubtype_Some_inv in Sub.
        destruct Sub as [env2' [[Eq Sub] | [T [Eq [SubT Sub]]]]].
        * subst; repeat constructor; now apply IHenv.
        * subst; constructor.
          -- eapply Subtype_Second; eassumption.
          -- now apply IHenv.
      + apply EnvironmentSubtype_None_inv in Sub.
        destruct Sub as [env2' [-> Sub]].
        inversion S; subst.
        repeat constructor; now apply IHenv.
  Qed.

  Lemma EnvironmentCombination_Second : forall env1 env2 env,
    SecondEnv env ->
    env1 ▷ₑ env2 ~= env ->
    SecondEnv env1 /\ SecondEnv env2.
  Proof.
    intros * S Comb.
    induction Comb; inversion S as [| ? ? ? S']; subst;
    try (apply IHComb in S'; destruct S' as [S1 S2]);
    try now repeat constructor.
    inversion H0; subst.
    + inversion H; subst; now repeat constructor.
    + inversion H; subst.
      inversion H5; subst.
      now repeat constructor.
  Qed.

  Lemma lookup_EmptyEnv_None : forall env x,
    EmptyEnv env ->
    lookup x env = None.
  Proof.
    induction env; intros.
    - apply lookup_nil.
    - inversion H; subst; destruct x;
      (apply lookup_zero || rewrite lookup_successor_cons; now apply IHenv).
  Qed.

  Lemma EmptyEnv_tl : forall env, EmptyEnv env -> EmptyEnv (tl env).
  Proof.
    destruct env; intros Empty; simpl; inversion Empty; now subst.
  Qed.

  Lemma insert_EmptyEnv_injective : forall env1 env2 x1 x2 T1 T2,
    EmptyEnv env1 ->
    insert x1 T1 env1 = insert x2 T2 env2 ->
    x1 = x2 /\ T1 = T2 /\ EmptyEnv env2.
  Proof.
    intros until x1.
    revert env1 env2.
    induction x1, x2; intros * Empty Eq;
    repeat try (rewrite raw_insert_zero in Eq);
    repeat try (rewrite raw_insert_successor in Eq);
    inversion Eq as [Eq']; subst.
    - easy.
    - now apply insert_EmptyEnv in Empty.
    - now rewrite lookup_EmptyEnv_None in Eq' by assumption.
    - generalize (EmptyEnv_tl env1 Empty); intros Empty'.
      generalize (IHx1 (tl env1) (tl env2) x2 T1 T2 Empty' H).
      intros [<- [<- Empty2]]; repeat split.
      destruct env2; constructor; simpl in *.
      + rewrite (lookup_EmptyEnv_None) in Eq' by assumption.
        now rewrite lookup_zero in Eq'.
      + assumption.
  Qed.

  Lemma EnvDis_EmptyEnv_left : forall env1 env2 env,
    EmptyEnv env1 ->
    env1 +ₑ env2 ~= env ->
    env2 = env.
  Proof.
    induction env1; intros * Empty Dis.
    - now inversion Dis.
    - inversion Empty; subst.
      inversion Dis; subst; f_equal; apply IHenv1; assumption.
  Qed.

  Lemma EnvDis_EmptyEnv_right : forall env1 env2 env,
    EmptyEnv env2 ->
    env1 +ₑ env2 ~= env ->
    env1 = env.
  Proof.
    intros env1 env2; revert env1.
    induction env2; intros * Empty Dis.
    - now inversion Dis.
    - inversion Empty; subst.
      inversion Dis; subst; f_equal; apply IHenv2; assumption.
  Qed.

  Lemma EnvDis_nil_left_inv : forall env1 env2,
    [] +ₑ env1 ~= env2 -> env1 = [] /\ env2 = [].
  Proof.
    induction env1; intros * Dis; now inversion Dis.
  Qed.

  Lemma EnvironmentDis_Some_inv : forall env1 env2 env T,
    Some T :: env1 +ₑ env2 ~= env ->
    Some T :: env1 +ₑ None :: tl env2 ~= Some T :: tl env.
  Proof.
    destruct env1; intros * Dis;
    inversion Dis; subst; now constructor.
  Qed.

  Lemma EnvironmentDis_Some_inv' : forall env1 env2 env T,
    Some T :: env1 +ₑ env2 ~= env ->
    exists env2' env',
    env = Some T :: env' /\
    env1 +ₑ env2' ~= env' /\
    (env2 = None :: env2' \/ exists BT, env2 = Some (TUBase BT) :: env2').
  Proof.
    intros * Dis; inversion Dis; subst;
    exists env3, env4; repeat split; eauto with environment.
  Qed.

  Lemma EnvDis_Sub : forall env1 env2 env1' env2' env,
    env1 ≤ₑ env1' ->
    env2 ≤ₑ env2' ->
    env1 +ₑ env2 ~= env ->
    exists env', env ≤ₑ env' /\ env1' +ₑ env2' ~= env'.
  Proof.
    intros * Sub1 Sub2 Dis.
    revert env1' env2' Sub1 Sub2.
    induction Dis; intros * Sub1 Sub2.
    - apply EnvironmentSubtype_nil_left in Sub1;
      apply EnvironmentSubtype_nil_left in Sub2; subst.
      exists []; eauto with environment.
    - do 2 simpl_SubEnv.
      generalize (IHDis _ _ Sub0 Sub).
      intros [env' [? ?]].
      exists (None :: env'); eauto with environment.
    - do 2 simpl_SubEnv; subst.
      + generalize (IHDis _ _ EnvSub Sub);
        intros [env' [? ?]];
        exists (None :: env'); repeat split;
        try (eapply EnvSubtypeTrans with (env2 := Some T0 :: env));
        eauto with environment.
      + generalize (IHDis _ _ EnvSub Sub);
        intros [env' [? ?]].
        exists (Some T0 :: env'); repeat split;
        eauto with environment.
    - do 2 simpl_SubEnv; subst.
      + generalize (IHDis _ _ Sub EnvSub);
        intros [env' [? ?]];
        exists (None :: env'); repeat split;
        try (eapply EnvSubtypeTrans with (env2 := Some T0 :: env));
        eauto with environment.
      + generalize (IHDis _ _ Sub EnvSub);
        intros [env' [? ?]];
        exists (Some T0 :: env'); repeat split;
        eauto with environment.
    - do 2 simpl_SubEnv; subst.
      + generalize (IHDis _ _ EnvSub0 EnvSub);
        intros [env' [? ?]];
        exists (None :: env'); repeat split;
        try (eapply EnvSubtypeTrans with (env2 := Some T0 :: env));
        eauto with environment.
      + generalize (IHDis _ _ EnvSub0 EnvSub);
        intros [env' [? ?]];
        exists (Some T0 :: env'); repeat split;
        eauto with environment.
      + inversion Sub; inversion Sub0; subst;
        generalize (IHDis _ _ EnvSub0 EnvSub);
        intros [env' [? ?]];
        exists (Some (TUBase BT) :: env'); repeat split;
        eauto with environment.
      + inversion Sub; inversion Sub0; subst;
        generalize (IHDis _ _ EnvSub0 EnvSub);
        intros [env' [? ?]];
        exists (Some (TUBase BT) :: env'); repeat split;
        eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_EmptyEnv_insert : forall env x T,
    insert x T env ≤ₑ create_EmptyEnv (insert x T env) ->
    env ≤ₑ create_EmptyEnv env.
  Proof.
    induction env; intros * Sub.
    - constructor.
    - simpl in *.
      destruct x.
      + repeat rewrite raw_insert_zero in Sub; simpl in *.
        simpl_SubEnv.
        * inversion Eq; subst; assumption.
        * inversion Eq.
      + rewrite raw_insert_successor in Sub;
        rewrite lookup_zero in Sub;
        simpl in *; destruct a.
        * simpl_SubEnv; subst.
          -- inversion Eq; subst.
             eapply EnvSubtypeTrans.
             ++ eapply EnvSubtypeSub. eassumption. apply EnvironmentSubtype_refl.
             ++ eapply EnvSubtypeUn.
                assumption.
                eapply IHenv; eassumption.
          -- inversion Eq.
        * constructor; apply EnvironmentSubtype_None_None_inv in Sub;
          eapply IHenv; eassumption.
  Qed.

  Lemma insert_Sub_EmptyEnv_inv : forall x T env env',
    EmptyEnv env' ->
    (insert x T env) ≤ₑ env' ->
    exists T', Unrestricted T' /\ T ≤ T'.
  Proof.
    induction x.
    - intros * Empty Sub.
      rewrite raw_insert_zero in Sub.
      simpl_SubEnv; subst.
      + now exists T0.
      + inversion Empty; subst; discriminate.
    - intros * Empty Sub.
      rewrite raw_insert_successor in Sub.
      destruct (lookup 0 env).
      + simpl_SubEnv; subst.
        * inversion Empty; subst.
          eapply IHx; eassumption.
        * inversion Empty; subst; discriminate.
      + simpl_SubEnv; subst.
        inversion Empty; subst.
        eapply IHx; eassumption.
  Qed.

  Lemma EnvironmentSubtype_EmptyEnv_insert_Un : forall env x T T',
    T ≤ T' ->
    Unrestricted T' ->
    EmptyEnv env ->
    insert x T env ≤ₑ create_EmptyEnv (insert x T env).
  Proof.
    induction env; intros * Sub Un Empty.
    - induction x.
      + rewrite raw_insert_zero; simpl;
        eapply EnvSubtypeTrans with (env2 := [Some T']);
        eauto with environment.
      + rewrite raw_insert_successor.
        rewrite lookup_nil; simpl;
        now constructor.
    - inversion Empty; subst.
      induction x.
      + rewrite raw_insert_zero; simpl.
        eapply EnvSubtypeTrans with (env2 := Some T' :: None :: env);
        eauto with environment.
      + rewrite raw_insert_successor; rewrite lookup_zero; simpl;
        eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_insert : forall env1 env2 x e,
    env1 ≤ₑ env2 ->
    (raw_insert x e env1) ≤ₑ (raw_insert x e env2).
  Proof.
    intros until x; revert env1 env2; induction x;
    intros * Sub.
    - repeat rewrite raw_insert_zero; destruct e;
      eauto using Subtype_refl with environment.
    - repeat rewrite raw_insert_successor;
      destruct env1, env2.
      + eauto using Subtype_refl with environment.
      + apply EnvironmentSubtype_nil_left in Sub; rewrite Sub;
        eauto using Subtype_refl with environment.
      + apply EnvironmentSubtype_nil_right in Sub; rewrite Sub;
        eauto using Subtype_refl with environment.
      + repeat rewrite lookup_zero; simpl.
        destruct o; simpl_SubEnv; inversion Eq; subst;
        try (eapply EnvSubtypeTrans with (env2 := Some T :: raw_insert x e env1));
        eauto using Subtype_refl with environment.
  Qed.

  Lemma EnvDis_insert_None : forall env1 env2 env x,
    env1 +ₑ env2 ~= env ->
    (raw_insert x None env1) +ₑ (raw_insert x None env2) ~= (raw_insert x None env).
  Proof.
    intros until x; revert env env1 env2; induction x; intros * Dis.
    - repeat rewrite raw_insert_zero; eauto with environment.
    - repeat rewrite raw_insert_successor.
      destruct env1, env2, env; simpl;
      repeat rewrite lookup_nil;
      repeat rewrite lookup_zero; try (destruct o); try inversion Dis; subst;
      eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_EmptyEnv_insert_None : forall env1 env2 x,
    EmptyEnv env2 ->
    raw_insert x None env1 ≤ₑ env2 ->
    exists env2', EmptyEnv env2' /\ env1 ≤ₑ env2'.
  Proof.
    intros until x.
    revert env1 env2.
    induction x; intros * Empty Sub.
    - rewrite raw_insert_zero in Sub.
      simpl_SubEnv; inversion Empty; subst.
      now exists env2'.
    - rewrite raw_insert_successor in Sub.
      destruct env1.
      + exists []; split; eauto with environment; constructor.
      + rewrite lookup_zero in Sub; simpl in *.
        destruct o; simpl_SubEnv; subst.
        * inversion Empty; subst.
          generalize (IHx env1 env0 H2 EnvSub).
          intros [env2' [Empty' Sub']].
          exists (None :: env2'); split.
          now constructor.
          eapply EnvSubtypeTrans with (env2 := Some T :: env1);
          eauto with environment.
        * inversion Empty; subst; discriminate.
        * inversion Empty; subst.
          generalize (IHx env1 env2' H2 Sub0).
          intros [env2'' [Empty' Sub']].
          exists (None :: env2''); split;
          now constructor.
  Qed.

  Lemma EnvironmentSubtype_EmptyEnv_insert_contra : forall v T env1 env2,
    EmptyEnv env1 ->
    ~ (env1 ≤ₑ insert v T env2).
  Proof.
    induction v; intros * Empty Sub.
    - rewrite raw_insert_zero in Sub.
      inversion Empty; subst.
      + apply EnvironmentSubtype_nil_left in Sub; discriminate.
      + simpl_SubEnv; discriminate.
    - rewrite raw_insert_successor in Sub.
      inversion Empty; subst.
      + apply EnvironmentSubtype_nil_left in Sub; discriminate.
      + simpl_SubEnv; inversion Eq; subst.
        now generalize (IHv _ _ _ H0 Sub0).
  Qed.

  Lemma EnvironmentSubtype_raw_insert_insert : forall x v T env1 env2,
    EmptyEnv env2 ->
    raw_insert x None env1 ≤ₑ insert v T env2 ->
    v < x ->
    exists env2', EmptyEnv env2' /\ env1 ≤ₑ insert v T env2'.
  Proof.
    intros until v; revert x.
    induction v; intros * Empty EnvSub le.
    - rewrite raw_insert_zero in EnvSub.
      destruct x.
      + lia.
      + rewrite raw_insert_successor in EnvSub.
        destruct (lookup 0 env1) eqn: L1.
        * simpl_SubEnv; inversion Eq; subst.
          generalize (EnvironmentSubtype_EmptyEnv_insert_None _ _ _ Empty EnvSub0).
          intros [env2' [Empty' EnvSub']].
          exists (env2').
          rewrite raw_insert_zero.
          assert (env1' : env1 = Some t :: tl env1).
          {
            destruct env1.
            - now rewrite lookup_nil in L1.
            - rewrite lookup_zero in L1; now subst.
          }
          rewrite env1'.
          eauto with environment.
        * simpl_SubEnv; inversion Eq; subst.
    - rewrite raw_insert_successor in EnvSub.
      destruct x.
      + lia.
      + rewrite raw_insert_successor in EnvSub.
        destruct (lookup 0 env1) eqn:L1.
        simpl_SubEnv; inversion Eq; subst.
        * generalize (EmptyEnv_tl env2 Empty); intros Empty_tl.
          assert (le' : v < x) by lia.
          generalize (IHv _ _ _ _ Empty_tl EnvSub0 le').
          intros [env2' [Empty' SubEnv']].
          exists (None :: env2').
          rewrite raw_insert_successor.
          rewrite lookup_zero.
          simpl.
          assert (env1' : env1 = Some t :: tl env1).
          {
            destruct env1.
            - now rewrite lookup_nil in L1.
            - rewrite lookup_zero in L1. now subst.
          }
          rewrite env1'; split.
          -- now constructor.
          -- eapply EnvSubtypeTrans with (env2 := Some T0 :: tl env1);
             eauto with environment.
        * rewrite lookup_EmptyEnv_None in Eq by assumption.
          discriminate.
        * simpl_SubEnv; inversion Eq; subst.
          generalize (EmptyEnv_tl env2 Empty); intros Empty_tl.
          assert (le' : v < x) by lia.
          generalize (IHv _ _ _ _ Empty_tl Sub le').
          intros [env2' [Empty' SubEnv']].
          exists (None :: env2').
          rewrite raw_insert_successor.
          rewrite lookup_zero.
          simpl.
          assert (env1' : env1 = None :: tl env1).
          {
            destruct env1.
            - simpl in *. apply EnvironmentSubtype_nil_left in SubEnv'.
              now apply insert_nil in SubEnv'.
            - rewrite lookup_zero in L1; now subst.
          }
          rewrite env1'; split.
          -- now constructor.
          -- eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_raw_insert_insert' : forall x v T env1 env2,
    EmptyEnv env2 ->
    raw_insert x None env1 ≤ₑ insert v T env2 ->
    v > x ->
    exists env2', EmptyEnv env2' /\ env1 ≤ₑ insert (v - 1) T env2'.
  Proof.
    intros until v; revert x.
    induction v; intros * Empty EnvSub le.
    - inversion le.
    - rewrite raw_insert_successor in EnvSub.
      generalize (EmptyEnv_tl env2 Empty); intros Empty_tl.
      assert (z : v - 0 = v) by lia.
      destruct x.
      + rewrite raw_insert_zero in EnvSub.
        simpl_SubEnv; inversion Eq; subst.
        exists (tl env2); simpl.
        rewrite z.
        auto.
      + rewrite raw_insert_successor in EnvSub.
        assert (le' : v > x) by lia.
        destruct (lookup 0 env1) eqn:L1.
        * assert (env1' : env1 = Some t :: tl env1).
          {
            destruct env1.
            - now rewrite lookup_nil in L1.
            - rewrite lookup_zero in L1. now subst.
          }
          rewrite env1'.
          simpl_SubEnv; inversion Eq; subst.
          -- generalize (IHv _ _ _ _ Empty_tl EnvSub0 le').
             intros [env2' [Empty' EnvSub']].
             exists (None :: env2').
             assert (E : S v - 1 = S (v - 1)) by lia.
             rewrite E.
             rewrite raw_insert_successor.
             rewrite lookup_zero.
             simpl.
             split.
             ++ now constructor.
             ++ eapply EnvSubtypeTrans with (env2 := Some T0 :: tl env1);
                eauto with environment.
          -- apply lookup_EmptyEnv_None with (x := 0) in Empty.
             rewrite Empty in *; discriminate.
        * simpl_SubEnv; inversion Eq; subst.
          assert (env1' : env1 = None :: tl env1).
          {
            destruct env1.
            - simpl in *.
              apply EnvironmentSubtype_EmptyEnv_insert_contra in Sub.
              now exfalso.
              induction x.
              + rewrite raw_insert_zero; repeat constructor.
              + apply EmptyEnv_raw_insert_None; constructor.
            - rewrite lookup_zero in L1; now subst.
          }
          rewrite env1'.
          generalize (IHv _ _ _ _ Empty_tl Sub le').
          intros [env2' [Empty' EnvSub']].
          exists (None :: env2').
          assert (E : S v - 1 = S (v - 1)) by lia.
          rewrite E.
          rewrite raw_insert_successor.
          rewrite lookup_zero.
          simpl.
          split.
          ++ now constructor.
          ++ eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_insert_None_Some : forall env1 env2 x T,
    ~ (raw_insert x None env1 ≤ₑ insert x T env2).
  Proof.
    intros until x.
    revert env1 env2.
    induction x; intros * Sub.
    - repeat rewrite raw_insert_zero in Sub.
      now apply EnvironmentSubtype_None_Some in Sub.
    - unfold not in IHx.
      repeat rewrite raw_insert_successor in Sub;
      destruct env1, env2;
      repeat rewrite lookup_nil in Sub;
      repeat rewrite lookup_zero in Sub;
      simpl in *.
      + simpl_SubEnv; inversion Eq; subst; eauto.
      + destruct o.
        * now apply EnvironmentSubtype_None_Some in Sub.
        * simpl_SubEnv; inversion Eq; subst; eauto.
      + destruct o; simpl_SubEnv; subst; inversion Eq; subst; eauto.
      + destruct o, o0; simpl_SubEnv; try inversion Eq; subst;
        eauto.
  Qed.

  Lemma EnvironmentDisjointCombination_remove_weaken_first : forall x env1 env2 env3 T1 T2,
    insert 0 T1 env1 +ₑ insert (S x) T2 (raw_insert 0 None env2) ~= insert 0 T1 env3 ->
    env1 +ₑ insert x T2 env2 ~= env3.
  Proof.
    induction x; intros * Dis.
    - repeat rewrite raw_insert_zero in *.
      rewrite raw_insert_successor in *; simpl in *.
      rewrite raw_insert_zero in *.
      rewrite lookup_zero in *.
      now inversion Dis; subst.
    - repeat rewrite raw_insert_zero in *.
      rewrite raw_insert_successor in *; simpl in *.
      repeat rewrite raw_insert_successor in *; simpl in *.
      destruct env2.
      + repeat rewrite lookup_zero in *; simpl in *.
        now inversion Dis; subst.
      + repeat rewrite lookup_zero in *; simpl in *.
        now inversion Dis; subst.
  Qed.

  Lemma EnvironmentCombination_Disjoint_Empty : forall env1 env2 env env3 env1' env2',
    EmptyEnv env ->
    env1 +ₑ env ~= env1' ->
    env2 +ₑ env ~= env2' ->
    env1' ▷ₑ env2' ~= env3 ->
    env1 ▷ₑ env2 ~= env3 /\ env3 +ₑ env ~= env3.
  Proof.
    intros * Empty Dis1 Dis2 Comb.
    generalize (EnvDis_EmptyEnv_right _ _ _ Empty Dis1).
    generalize (EnvDis_EmptyEnv_right _ _ _ Empty Dis2).
    intros -> ->; split.
    assumption.
    (* TODO: Create lemma *)
    revert env Dis1 Dis2 Empty.
    induction Comb; intros; inversion Dis1; subst; inversion Dis2; subst;
    try constructor;
    try apply IHComb; try assumption; try now inversion Empty; subst.
  Qed.

  Lemma EnvironmentCombination_raw_insert_insert : forall x T1 T2 T env1 env2 env3,
    T1 ▷ T2 ~= T ->
    raw_insert x None env1 ▷ₑ raw_insert x None env2 ~= raw_insert x None env3 ->
    insert x T1 env1 ▷ₑ insert x T2 env2 ~= insert x T env3.
  Proof.
    induction x; intros * CombT Comb.
    - repeat rewrite raw_insert_zero in *.
      inversion Comb; subst.
      now constructor.
    - repeat rewrite raw_insert_successor in *.
      destruct env1, env2, env3; simpl in *;
      try repeat rewrite lookup_nil in *;
      try repeat rewrite lookup_zero in *;
      inversion Comb; subst;
      try constructor; try now apply IHx.
      assumption.
  Qed.

  Lemma EnvironmentDisjointCombination_insert_left : forall x T env1 env2 env3,
    insert x T env1 +ₑ env2 ~= env3 ->
    exists env2' env3',
      (env2 = raw_insert x None env2' /\ env3 = insert x T env3') \/
      (exists c, env2 = insert x T env2' /\ env3 = insert x T env3' /\ T = TUBase c).
  Proof.
    induction x; intros * Dis.
    - rewrite raw_insert_zero in Dis.
      inversion Dis; subst; exists env4, env.
      + left; now repeat rewrite raw_insert_zero.
      + right; exists BT; now repeat rewrite raw_insert_zero.
    - rewrite raw_insert_successor in Dis.
      destruct env1.
      + rewrite lookup_nil in *; simpl in *.
        inversion Dis; subst.
        * generalize (IHx _ _ _ _ H0).
          intros [env2' [env3' [[-> ->] | [c [-> [-> ->]]]]]];
          exists (None :: env2'), (None :: env3').
          -- left; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
          -- right; exists c; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
        * generalize (IHx _ _ _ _ H0).
          intros [env2' [env3' [[-> ->] | [c [-> [-> ->]]]]]];
          exists (Some T0 :: env2'), (Some T0 :: env3').
          -- left; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
          -- right; exists c; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
      + rewrite lookup_zero in *; simpl in *.
        inversion Dis; subst.
        * generalize (IHx _ _ _ _ H3).
          intros [env2' [env3' [[-> ->] | [c [-> [-> ->]]]]]];
          exists (None :: env2'), (None :: env3').
          -- left; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
          -- right; exists c; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
        * generalize (IHx _ _ _ _ H3).
          intros [env2' [env3' [[-> ->] | [c [-> [-> ->]]]]]];
          exists (None :: env2'), (Some T0 :: env3').
          -- left; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
          -- right; exists c; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
        * generalize (IHx _ _ _ _ H3).
          intros [env2' [env3' [[-> ->] | [c [-> [-> ->]]]]]];
          exists (Some T0 :: env2'), (Some T0 :: env3').
          -- left; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
          -- right; exists c; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
        * generalize (IHx _ _ _ _ H3).
          intros [env2' [env3' [[-> ->] | [c [-> [-> ->]]]]]];
          exists (Some (TUBase BT) :: env2'), (Some (TUBase BT) :: env3').
          -- left; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
          -- right; exists c; repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero.
  Qed.

  Lemma EnvironmentCombination_insert_insert_None : forall x v A1 A2 A env1 env2 env3,
    insert x A1 env1 ▷ₑ insert x A2 env2 ~= insert x A (raw_insert v None env3) ->
    exists env1' env2',
      insert x A1 env1 = insert x A1 (raw_insert v None env1') /\
      insert x A2 env2 = insert x A2 (raw_insert v None env2').
  Proof.
    induction x; intros * Comb.
    - repeat rewrite raw_insert_zero in *.
      inversion Comb; subst.
      apply EnvironmentCombination_raw_insert_None in H2.
      destruct H2 as [env1' [env2' [-> [? [-> [? Comb']]]]]].
      now exists env1', env2'; repeat rewrite raw_insert_zero.
    - destruct v.
      + repeat rewrite raw_insert_successor in *.
        repeat rewrite raw_insert_zero in *.
        repeat rewrite lookup_zero in *.
        simpl in *.
        inversion Comb; subst.
        exists (tl env1), (tl env2).
        repeat rewrite raw_insert_successor.
        repeat rewrite raw_insert_zero.
        now repeat rewrite lookup_zero.
      + repeat rewrite raw_insert_successor in *.
        inversion Comb; subst.
        * generalize (IHx _ _ _ _ _ _ _ H0).
          intros [env1' [env2' [Eq1 Eq2]]].
          rewrite Eq1; rewrite Eq2.
          exists (None :: env1'), (None :: env2').
          repeat rewrite raw_insert_successor.
          now repeat rewrite lookup_zero.
        * generalize (IHx _ _ _ _ _ _ _ H0).
          intros [env1' [env2' [Eq1 Eq2]]].
          rewrite Eq1; rewrite Eq2.
          exists (Some T :: env1'), (None :: env2').
          repeat rewrite raw_insert_successor.
          now repeat rewrite lookup_zero.
        * generalize (IHx _ _ _ _ _ _ _ H0).
          intros [env1' [env2' [Eq1 Eq2]]].
          rewrite Eq1; rewrite Eq2.
          exists (None :: env1'), (Some T :: env2').
          repeat rewrite raw_insert_successor.
          now repeat rewrite lookup_zero.
        * generalize (IHx _ _ _ _ _ _ _ H2).
          intros [env1' [env2' [Eq1 Eq2]]].
          rewrite Eq1; rewrite Eq2.
          exists (Some T1 :: env1'), (Some T2 :: env2').
          repeat rewrite raw_insert_successor.
          now repeat rewrite lookup_zero.
  Qed.

  Lemma EnvironmentSubtype_tl : forall env1 env2, env1 ≤ₑ env2 -> tl env1 ≤ₑ tl env2.
  Proof.
    intros * Sub; induction Sub; eauto using EnvironmentSubtype_trans with environment.
  Qed.

  Lemma EnvironmentDisjointCombination_second_None : forall T1 T2 env1 env2 env3,
    T1 :: env1 +ₑ None :: env2 ~= T2 :: env3 -> T1 = T2.
  Proof.
    intros * Comb; now inversion Comb; subst.
  Qed.

  Lemma EnvironmentDisjointCombination_second_Some : forall T1 T2 T3 env1 env2 env3,
    T1 :: env1 +ₑ Some T2 :: env2 ~= T3 :: env3 ->
    (T1 = None /\ T3 = Some T2) \/ (exists c, T1 = Some (TUBase c) /\ T2 = TUBase c /\ T3 = Some (TUBase c)).
  Proof.
    intros * Comb; inversion Comb; subst.
    - auto.
    - right; exists BT; auto.
  Qed.

  Lemma EnvironmentDisjointCombination_Subtype_Empty : forall env1 env1' env2 env3,
    env1 +ₑ env2 ~= env3 ->
    EmptyEnv env1' ->
    env1 ≤ₑ env1' ->
    env3 ≤ₑ env2.
  Proof.
    intros * Comb; revert env1'.
    induction Comb; intros * Empty Sub.
    - constructor.
    - constructor.
      apply EnvironmentSubtype_None_inv in Sub.
      destruct Sub as [env2' [-> Sub]].
      inversion Empty; eapply IHComb; eassumption.
    - apply EnvironmentSubtype_Some_inv' in Sub.
      destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
      + eapply EnvironmentSubtype_trans with (env2 := Some T' :: env);
        inversion Empty; try constructor; eauto with environment.
      + inversion Empty; discriminate.
    - apply EnvironmentSubtype_None_inv in Sub.
      destruct Sub as [env2' [-> Sub]].
      constructor; inversion Empty; eauto using Subtype_refl with environment.
    - apply EnvironmentSubtype_Some_inv' in Sub.
      destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
      + constructor; inversion Empty; eauto using Subtype_refl with environment.
      + inversion Empty; discriminate.
  Qed.

  Lemma EnvironmentDisjointCombination_Subtype_Empty_insert : forall x T env1 env1' env2 env3,
    insert x T env1 +ₑ raw_insert x None env2 ~= insert x T env3 ->
    EmptyEnv env1' ->
    env1 ≤ₑ env1' ->
    insert x T env3 ≤ₑ insert x T env2.
  Proof.
    induction x; intros * Comb Empty Sub .
    - repeat rewrite raw_insert_zero in *.
      inversion Comb; subst.
      constructor; try apply Subtype_refl.
      revert env1' Sub Empty.
      induction H0; intros; try rename IHEnvironmentDisjointCombination into IH.
      + constructor.
      + constructor.
        apply EnvironmentSubtype_None_inv in Sub.
        destruct Sub as [envT [-> Sub]].
        eapply IH.
        * now constructor.
        * eassumption.
        * now inversion Empty.
      + apply EnvironmentSubtype_Some_inv' in Sub.
        destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
        * eapply EnvironmentSubtype_trans with (env2 := Some T' :: env); eauto with environment.
          constructor; try assumption.
          eapply IH.
          -- now constructor.
          -- eassumption.
          -- now inversion Empty.
        * inversion Empty; discriminate.
      + constructor; try apply Subtype_refl.
        apply EnvironmentSubtype_None_inv in Sub.
        destruct Sub as [envT [-> Sub]].
        eapply IH.
        * now constructor.
        * eassumption.
        * now inversion Empty.
      + repeat constructor.
        apply EnvironmentSubtype_Some_inv' in Sub.
        destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
        * eapply IH.
          -- now constructor.
          -- eassumption.
          -- now inversion Empty.
        * inversion Empty; discriminate.
    - repeat rewrite raw_insert_successor in *.
      destruct env2, env3; simpl in *.
      + repeat rewrite lookup_nil in *.
        now constructor.
      + repeat rewrite lookup_zero in *.
        rewrite lookup_nil in *.
        destruct env1.
        * apply EnvironmentSubtype_nil_left in Sub.
          subst.
          rewrite lookup_nil in Comb.
          inversion Comb; subst.
          constructor.
          eapply IHx; try eassumption; constructor.
        * rewrite lookup_zero in Comb.
          simpl in *.
          generalize (EnvironmentDisjointCombination_second_None _ _ _ _ _ Comb).
          intros ->.
          destruct o.
          -- apply EnvironmentSubtype_Some_inv' in Sub.
             destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
             ++ eapply EnvironmentSubtype_trans with (env2 := Some T' :: insert x T env3).
                eauto with environment.
                constructor; try assumption.
                eapply IHx.
                ** inversion Comb; subst; eassumption.
                ** inversion Empty; subst; apply H2.
                ** assumption.
             ++ inversion Empty; discriminate.
          -- apply EnvironmentSubtype_None_inv in Sub.
             destruct Sub as [env2' [-> Sub]].
             inversion Comb; subst; constructor.
             eapply IHx; try (inversion Empty; subst); eassumption.
      + repeat rewrite lookup_nil in *.
        repeat rewrite lookup_zero in *.
        destruct env1.
        * rewrite lookup_nil in *.
          apply EnvironmentSubtype_nil_left in Sub; subst.
          apply EnvironmentDis_Comb_comm in Comb.
          generalize (EnvironmentDisjointCombination_second_None _ _ _ _ _ Comb).
          intros ->; constructor.
          inversion Comb; subst.
          apply EnvironmentDis_Comb_comm in H2.
          eapply IHx; try eassumption; constructor.
        * rewrite lookup_zero in *; simpl in *.
          inversion Comb; subst.
          constructor.
          apply EnvironmentSubtype_None_inv in Sub.
          destruct Sub as [env2' [-> Sub]].
          eapply IHx.
          -- eassumption.
          -- inversion Empty; apply H3.
          -- eassumption.
      + repeat rewrite lookup_zero in *.
        destruct env1.
        * rewrite lookup_nil in *.
          apply EnvironmentDis_Comb_comm in Comb.
          generalize (EnvironmentDisjointCombination_second_None _ _ _ _ _ Comb).
          intros ->.
          apply EnvironmentSubtype_nil_left in Sub; subst.
          destruct o0; constructor; try apply Subtype_refl;
          inversion Comb; subst.
          -- apply EnvironmentDis_Comb_comm in H0.
             eapply IHx; try eassumption; constructor.
          -- apply EnvironmentDis_Comb_comm in H2.
             eapply IHx; try eassumption; constructor.
        * rewrite lookup_zero in *; simpl in *.
          destruct o.
          -- generalize (EnvironmentDisjointCombination_second_Some _ _ _ _ _ _ Comb).
             intros [[-> ->] | [c [-> [-> ->]]]].
             ++ apply EnvironmentSubtype_None_inv in Sub.
                destruct Sub as [env2' [-> Sub]].
                inversion Empty.
                inversion Comb; subst.
                constructor; try apply Subtype_refl.
                eapply IHx; try eassumption.
             ++ inversion Comb; subst.
                constructor; try apply Subtype_refl.
                apply EnvironmentSubtype_Some_inv' in Sub.
                destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
                ** inversion Empty; eapply IHx; try eassumption.
                ** inversion Empty; discriminate.
          -- generalize (EnvironmentDisjointCombination_second_None _ _ _ _ _ Comb).
             intros ->.
             destruct o0.
             ++ inversion Comb; subst.
                apply EnvironmentSubtype_Some_inv' in Sub.
                destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
                ** eapply EnvironmentSubtype_trans with (env2 := Some T' :: insert x T env3).
                   eauto with environment.
                   constructor; try assumption.
                   inversion Empty.
                   eapply IHx with (env1' := envT); try eassumption.
                ** inversion Empty; discriminate.
             ++ inversion Comb; subst.
                apply EnvironmentSubtype_None_inv in Sub.
                destruct Sub as [env2' [-> Sub]].
                constructor; inversion Empty.
                eapply IHx with (env1' := env2'); try eassumption.
  Qed.

  Lemma EnvironmentDisjointCombination_Subtype_Empty_insert_Base : forall x c env1 env1' env2 env3,
    insert x (TUBase c) env1 +ₑ insert x (TUBase c) env2 ~= insert x (TUBase c) env3 ->
    EmptyEnv env1' ->
    env1 ≤ₑ env1' ->
    insert x (TUBase c) env3 ≤ₑ insert x (TUBase c) env2.
  Proof.
    induction x; intros * Comb Empty Sub.
    - repeat rewrite raw_insert_zero in *.
      inversion Comb; subst.
      constructor; try apply Subtype_refl.
      revert env1' Sub Empty.
      induction H0; intros; try rename IHEnvironmentDisjointCombination into IH.
      + constructor.
      + constructor.
        apply EnvironmentSubtype_None_inv in Sub.
        destruct Sub as [envT [-> Sub]].
        eapply IH.
        * now constructor.
        * eassumption.
        * now inversion Empty.
      + apply EnvironmentSubtype_Some_inv' in Sub.
        destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
        * eapply EnvironmentSubtype_trans with (env2 := Some T' :: env); eauto with environment.
          constructor; try assumption.
          eapply IH.
          -- now constructor.
          -- eassumption.
          -- now inversion Empty.
        * inversion Empty; discriminate.
      + constructor; try apply Subtype_refl.
        apply EnvironmentSubtype_None_inv in Sub.
        destruct Sub as [envT [-> Sub]].
        eapply IH.
        * now constructor.
        * eassumption.
        * now inversion Empty.
      + repeat constructor.
        apply EnvironmentSubtype_Some_inv' in Sub.
        destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
        * eapply IH.
          -- now constructor.
          -- eassumption.
          -- now inversion Empty.
        * inversion Empty; discriminate.
    - repeat rewrite raw_insert_successor in *.
      destruct env2, env3; simpl in *.
      + repeat rewrite lookup_nil in *.
        now constructor.
      + repeat rewrite lookup_zero in *.
        rewrite lookup_nil in *.
        destruct env1.
        * apply EnvironmentSubtype_nil_left in Sub.
          subst.
          rewrite lookup_nil in Comb.
          inversion Comb; subst.
          constructor.
          eapply IHx; try eassumption; constructor.
        * rewrite lookup_zero in Comb.
          simpl in *.
          generalize (EnvironmentDisjointCombination_second_None _ _ _ _ _ Comb).
          intros ->.
          destruct o.
          -- apply EnvironmentSubtype_Some_inv' in Sub.
             destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
             ++ eapply EnvironmentSubtype_trans with (env2 := Some T' :: insert x (TUBase c) env3).
                eauto with environment.
                constructor; try assumption.
                eapply IHx.
                ** inversion Comb; subst; eassumption.
                ** inversion Empty; subst; apply H2.
                ** assumption.
             ++ inversion Empty; discriminate.
          -- apply EnvironmentSubtype_None_inv in Sub.
             destruct Sub as [env2' [-> Sub]].
             inversion Comb; subst; constructor.
             eapply IHx; try (inversion Empty; subst); eassumption.
      + repeat rewrite lookup_nil in *.
        repeat rewrite lookup_zero in *.
        destruct env1.
        * rewrite lookup_nil in *.
          apply EnvironmentSubtype_nil_left in Sub; subst.
          apply EnvironmentDis_Comb_comm in Comb.
          generalize (EnvironmentDisjointCombination_second_None _ _ _ _ _ Comb).
          intros ->; constructor.
          inversion Comb; subst.
          apply EnvironmentDis_Comb_comm in H2.
          eapply IHx; try eassumption; constructor.
        * rewrite lookup_zero in *; simpl in *.
          inversion Comb; subst.
          constructor.
          apply EnvironmentSubtype_None_inv in Sub.
          destruct Sub as [env2' [-> Sub]].
          eapply IHx.
          -- eassumption.
          -- inversion Empty; apply H3.
          -- eassumption.
      + repeat rewrite lookup_zero in *.
        destruct env1.
        * rewrite lookup_nil in *.
          apply EnvironmentDis_Comb_comm in Comb.
          generalize (EnvironmentDisjointCombination_second_None _ _ _ _ _ Comb).
          intros ->.
          apply EnvironmentSubtype_nil_left in Sub; subst.
          destruct o0; constructor; try apply Subtype_refl;
          inversion Comb; subst.
          -- apply EnvironmentDis_Comb_comm in H0.
             eapply IHx; try eassumption; constructor.
          -- apply EnvironmentDis_Comb_comm in H2.
             eapply IHx; try eassumption; constructor.
        * rewrite lookup_zero in *; simpl in *.
          destruct o.
          -- generalize (EnvironmentDisjointCombination_second_Some _ _ _ _ _ _ Comb).
             intros [[-> ->] | [c' [-> [-> ->]]]].
             ++ apply EnvironmentSubtype_None_inv in Sub.
                destruct Sub as [env2' [-> Sub]].
                inversion Empty.
                inversion Comb; subst.
                constructor; try apply Subtype_refl.
                eapply IHx; try eassumption.
             ++ inversion Comb; subst.
                constructor; try apply Subtype_refl.
                apply EnvironmentSubtype_Some_inv' in Sub.
                destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
                ** inversion Empty; eapply IHx; try eassumption.
                ** inversion Empty; discriminate.
          -- generalize (EnvironmentDisjointCombination_second_None _ _ _ _ _ Comb).
             intros ->.
             destruct o0.
             ++ inversion Comb; subst.
                apply EnvironmentSubtype_Some_inv' in Sub.
                destruct Sub as [envT [T' [SubT [Sub [[-> Unr] | ->]]]]].
                ** eapply EnvironmentSubtype_trans with (env2 := Some T' :: insert x (TUBase c) env3).
                   eauto with environment.
                   constructor; try assumption.
                   inversion Empty.
                   eapply IHx with (env1' := envT); try eassumption.
                ** inversion Empty; discriminate.
             ++ inversion Comb; subst.
                apply EnvironmentSubtype_None_inv in Sub.
                destruct Sub as [env2' [-> Sub]].
                constructor; inversion Empty.
                eapply IHx with (env1' := env2'); try eassumption.
  Qed.


  Lemma EnvironmentCombination_insert_both : forall x env1 env2 env3 T1 T2 T,
    T1 ▷ T2 ~= T ->
    env1 ▷ₑ env2 ~= env3 ->
    insert x T1 env1 ▷ₑ insert x T2 env2 ~= insert x T env3.
  Proof.
    induction x; intros * TComb Comb.
    - repeat rewrite raw_insert_zero; now constructor.
    - repeat rewrite raw_insert_successor.
      destruct env1, env2, env3;
      repeat rewrite lookup_nil in *;
      repeat rewrite lookup_zero in *;
      simpl in *;
      try inversion Comb; subst;
      constructor; try assumption; now eapply IHx.
  Qed.

  Lemma EnvironmentDisjointCombination_Empty_right : forall env1 env2,
    EmptyEnv env2 ->
    length env1 = length env2 ->
    env1 +ₑ env2 ~= env1.
  Proof.
    induction env1, env2; intros Empty L;
    try (inversion L; fail); try constructor.
    destruct o.
    - inversion Empty; discriminate.
    - destruct a; inversion Empty; inversion L;
      constructor; now apply IHenv1.
  Qed.

  Lemma EnvironmentDisjointCombination_insert_EmptyEnv : forall x env1 env1' T,
    EmptyEnv env1' ->
    length env1 = length env1' ->
    raw_insert x None env1 +ₑ insert x T env1' ~= insert x T env1.
  Proof.
    induction x; intros * Empty L.
    - repeat rewrite raw_insert_zero.
      constructor.
      now apply EnvironmentDisjointCombination_Empty_right.
    - repeat rewrite raw_insert_successor.
      destruct env1, env1'.
      + repeat rewrite lookup_nil; constructor; simpl.
        now apply IHx.
      + inversion L.
      + inversion L.
      + repeat rewrite lookup_zero; simpl in *.
        inversion Empty; subst.
        inversion L.
        destruct o; constructor; now apply IHx.
  Qed.

  Lemma EnvironmentDisjointCombination_insert_Base : forall x env1 env1' c,
    EmptyEnv env1' ->
    length env1 = length env1' ->
    insert x (TUBase c) env1 +ₑ insert x (TUBase c) env1' ~= insert x (TUBase c) env1.
  Proof.
    induction x; intros * Empty L.
    - repeat rewrite raw_insert_zero.
      constructor.
      now apply EnvironmentDisjointCombination_Empty_right.
    - repeat rewrite raw_insert_successor.
      destruct env1, env1'.
      + repeat rewrite lookup_nil; constructor; simpl.
        now apply IHx.
      + inversion L.
      + inversion L.
      + repeat rewrite lookup_zero; simpl in *.
        inversion Empty; subst.
        inversion L.
        destruct o; constructor; now apply IHx.
  Qed.

  Lemma EnvironmentSubtype_insert_Subtype : forall x T1 T2 env,
    T1 ≤ T2 ->
    insert x T1 env ≤ₑ insert x T2 env.
  Proof.
    induction x; intros * Sub.
    - repeat rewrite raw_insert_zero.
      constructor; eauto with environment.
    - repeat rewrite raw_insert_successor.
      destruct (lookup 0 env);
      constructor; try apply Subtype_refl; now apply IHx.
  Qed.

  Lemma EnvironmentDisjointCombination_Empty : forall env1 env2,
    EmptyEnv env2 ->
    length env1 = length env2 ->
    env1 +ₑ env2 ~= env1.
  Proof.
    induction env1, env2; intros Empty L.
    - constructor.
    - inversion L.
    - inversion L.
    - inversion Empty; inversion L; subst;
      destruct a; constructor;
      now apply IHenv1.
  Qed.

  Lemma EnvironmentSubtype_create_EmptyEnv_left : forall env1 env2,
    env1 ≤ₑ env2 ->
    env2 ≤ₑ create_EmptyEnv env2 ->
    env1 ≤ₑ create_EmptyEnv env1.
  Proof.
    induction env1, env2; intros EnvSub1 EnvSub2; simpl in *.
    - constructor.
    - constructor.
    - now apply EnvironmentSubtype_cons_nil in EnvSub1.
    - destruct a, o.
      + apply EnvironmentSubtype_Some_Some_inv in EnvSub1.
        destruct EnvSub1 as [Sub EnvSub].
        apply EnvironmentSubtype_Some_None_inv in EnvSub2.
        destruct EnvSub2 as [T' [Unr [Sub' EnvSub2]]].
        eapply EnvSubtypeTrans with (env2 := Some t0 :: env1).
        * eauto with environment.
        * eapply EnvSubtypeTrans with (env2 := Some T' :: env1);
          eauto with environment.
      + apply EnvironmentSubtype_Some_None_inv in EnvSub1.
        destruct EnvSub1 as [T' [Unr [Sub' EnvSub1]]].
        apply EnvironmentSubtype_None_None_inv in EnvSub2.
        eauto using EnvSubtypeTrans with environment.
      + now apply EnvironmentSubtype_None_Some in EnvSub1.
      + apply EnvironmentSubtype_None_None_inv in EnvSub1, EnvSub2.
        eauto using EnvSubtypeTrans with environment.
  Qed.

  Lemma EnvironmentSubtype_insert_Empty : forall x env1 env2 T1 T2,
    insert x T1 env1 ≤ₑ insert x T2 env2 ->
    env2 ≤ₑ create_EmptyEnv env2 ->
    env1 ≤ₑ create_EmptyEnv env1.
  Proof.
    induction x; intros * EnvSubI EnvSub.
    - repeat rewrite raw_insert_zero in EnvSubI.
      apply EnvironmentSubtype_Some_Some_inv in EnvSubI.
      destruct EnvSubI as [].
      eauto using EnvironmentSubtype_create_EmptyEnv_left.
    - repeat rewrite raw_insert_successor in EnvSubI.
      destruct env1, env2.
      + constructor.
      + constructor.
      + destruct o;
        repeat rewrite lookup_zero in EnvSubI;
        repeat rewrite lookup_nil in EnvSubI;
        simpl in *.
        * apply EnvironmentSubtype_Some_None_inv in EnvSubI.
          destruct EnvSubI as [T' [Unr [Sub' EnvSubI]]].
          eauto using EnvSubtypeTrans with environment.
        * apply EnvironmentSubtype_None_None_inv in EnvSubI.
          eauto with environment.
      + destruct o, o0; simpl in *;
        repeat rewrite lookup_zero in *;
        repeat rewrite lookup_nil in *;
        simpl in *.
        * apply EnvironmentSubtype_Some_None_inv in EnvSub.
          destruct EnvSub as [T' [Unr [Sub' EnvSub']]].
          apply EnvironmentSubtype_Some_Some_inv in EnvSubI.
          destruct EnvSubI as [Sub EnvSub].
          eapply EnvSubtypeTrans with (env2 := Some t0 :: env1);
          eauto using EnvSubtypeTrans with environment.
        * apply EnvironmentSubtype_Some_None_inv in EnvSubI.
          destruct EnvSubI as [T' [Unr [Sub' EnvSub']]].
          apply EnvironmentSubtype_None_None_inv in EnvSub.
          eauto using EnvSubtypeTrans with environment.
        * now apply EnvironmentSubtype_None_Some in EnvSubI.
        * apply EnvironmentSubtype_None_None_inv in EnvSubI, EnvSub.
          eauto with environment.
  Qed.

  Lemma EnvironmentSubtype_SecondClass : forall env, env ≤ₑ ⌈ env ⌉ₑ.
  Proof.
    induction env.
    - constructor.
    - destruct a; simpl; constructor; try apply Subtype_SecondClass; assumption.
  Qed.

  Lemma secondEnvironment_raw_insert_None : forall x env1 env2,
    ⌈ env1 ⌉ₑ = raw_insert x None env2 ->
    env2 = ⌈ env2 ⌉ₑ.
  Proof.
    induction x; intros * Eq.
    - rewrite raw_insert_zero in Eq.
      induction env1.
      + discriminate.
      + destruct a.
        * simpl in *.
          discriminate.
        * simpl in *.
          inversion Eq.
          now rewrite <- secondEnvironment_idem.
    - destruct env1 as [| T1 env1'], env2 as [| T2 env2']; try easy;
      rewrite raw_insert_successor in Eq;
      rewrite lookup_zero in Eq;
      simpl in *;
      inversion Eq;
      destruct T1; simpl in *;
      try rewrite <- secondUsage_idem;
      f_equal; now apply IHx with (env1 := env1').
  Qed.

  Lemma secondEnvironment_insert : forall x T env1 env2,
    ⌈ env1 ⌉ₑ = insert x T env2 ->
    env2 = ⌈ env2 ⌉ₑ /\ T = ⌈ T ⌉ⁿ.
  Proof.
    induction x; intros * Eq.
    - rewrite raw_insert_zero in Eq.
      destruct env1.
      + simpl in *; discriminate.
      + simpl in *.
        inversion Eq.
        destruct o.
        * simpl in *; inversion H0.
          rewrite <- secondEnvironment_idem.
          now rewrite <- secondUsage_idem.
        * now inversion H0.
    - destruct env1 as [| T1 env1'], env2 as [| T2 env2']; try easy.
      + rewrite raw_insert_successor in Eq.
        rewrite lookup_nil in Eq. simpl in *.
        inversion Eq.
        now apply IHx in H1.
      + rewrite raw_insert_successor in Eq.
        rewrite lookup_zero in Eq.
        inversion Eq.
        apply IHx in H1.
        destruct H1 as [Eq1 Eq2].
        subst.
        destruct T1; simpl in *.
        * rewrite <- secondUsage_idem; split; try f_equal; auto.
        * split; try f_equal; auto.
  Qed.

  Lemma secondEnvironment_nil : forall env,
    ⌈ env ⌉ₑ = ⌈ [] ⌉ₑ -> env = [].
  Proof.
    destruct env; intros * Eq; now try inversion H.
  Qed.

  Lemma secondEnvironment_raw_insert_None_inv : forall x env1 env2,
    ⌈ env1 ⌉ₑ = raw_insert x None ⌈ env2 ⌉ₑ ->
    exists env2', env1 = raw_insert x None env2' /\ ⌈ env2' ⌉ₑ = ⌈ env2 ⌉ₑ.
  Proof.
    induction x; intros * Eq.
    - rewrite raw_insert_zero in Eq.
      destruct env1.
      + discriminate.
      + simpl in *.
        inversion Eq.
        destruct o; simpl in *.
        * discriminate.
        * exists env1; now rewrite raw_insert_zero.
    - destruct env1 as [| T1 env1'], env2 as [| T2 env2']; try easy.
      + rewrite raw_insert_successor in *; simpl in *.
        rewrite lookup_nil in Eq.
        inversion Eq.
        destruct T1; try discriminate; simpl in *.
        assert (Eq' : ⌈ env1' ⌉ₑ = raw_insert x None ⌈ [] ⌉ₑ) by auto.
        apply IHx in Eq'.
        destruct Eq' as [env2' [Eq1' Eq2']].
        apply secondEnvironment_nil in Eq2'; subst.
        setoid_rewrite raw_insert_successor.
        exists []; rewrite lookup_nil; simpl; now f_equal.
      + simpl in *.
        rewrite raw_insert_successor in Eq.
        rewrite lookup_zero in Eq.
        simpl in *.
        inversion Eq as [TEq].
        apply IHx in H.
        destruct H as [env2'' [Eq1' Eq2']].
        subst.
        destruct T1, T2; simpl in *; try (inversion Eq; discriminate).
        * inversion TEq; subst.
          exists (Some t :: env2'').
          rewrite raw_insert_successor;
          rewrite lookup_zero;
          simpl.
          now rewrite Eq2'.
        * inversion TEq; subst.
          exists (None :: env2'').
          rewrite raw_insert_successor;
          rewrite lookup_zero;
          simpl.
          now rewrite Eq2'.
  Qed.

  Lemma EnvironmentSubtype_insert_T : forall x env T T',
    T' ≤ T -> insert x T' env ≤ₑ insert x T env.
  Proof.
    induction x; intros * Sub.
    - repeat rewrite raw_insert_zero; eauto with environment.
    - repeat rewrite raw_insert_successor.
      destruct env.
      + rewrite lookup_nil; eauto with environment.
      + rewrite lookup_zero; simpl.
        destruct o; eauto using Subtype_refl with environment.
  Qed.

End environment_properties.

Hint Resolve create_EmptyEnv_EmptyEnv : environment.
Hint Resolve SubEnv_EmptyEnv_create_EmptyEnv : environment.
Hint Resolve EnvironmentSubtype_nil_left : environment.
Hint Resolve EnvironmentSubtype_nil_right : environment.
Hint Resolve create_EmptyEnv_length_same : environment.
