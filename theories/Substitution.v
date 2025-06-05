(** * Substitution *)

From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.
From MailboxTypes Require Import TypingRules.
From MailboxTypes Require Import Dblib.DeBruijn.
(*From MailboxTypes Require Import Dblib.DblibTactics.*)

From Stdlib Require Import Lia.

(** We assume functional extensionality in order to proof statements about substitutions. *)
From Stdlib Require Import FunctionalExtensionality.

Generalizable All Variables.

(** ** Definitions *)
Section subs_def.

  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.


  Instance Var_Value : Var Value :=
  {
    var := ValueVar
  }.

  Definition traverse_Value (f : nat -> nat -> Value) l v :=
    match v with
    | ValueVar x => f l x
    | v' => v'
    end.

  Fixpoint traverse_Term (f : nat -> nat -> Value) l t :=
    match t with
    | TValue v => TValue (traverse_Value f l v)
    | TLet t1 t2  => TLet (traverse_Term f l t1) (traverse_Term f (l+1) t2)
    | TApp def v => TApp def (traverse_Value f l v)
   | TSpawn t1 => TSpawn (traverse_Term f l t1)
    | TNew => TNew
    | TSend v1 m v2 => TSend (traverse_Value f l v1) m (traverse_Value f l v2)
    | TGuard v e guards => TGuard (traverse_Value f l v) e (List.map (traverse_Guard f l) guards)
    end
  with traverse_Guard (f : nat -> nat -> Value) l g :=
match g with
    | GFail => GFail
    | GFree t1 => GFree (traverse_Term f l t1)
    (* Assumption: we only receive one value in the message *)
    | GReceive m t1 => GReceive m (traverse_Term f (l+2) t1)
    end.

  Instance Traverse_Value_Value : Traverse Value Value :=
  {
    traverse := traverse_Value
  }.

  Instance Traverse_Value_Term : Traverse Value Term :=
  {
    traverse := traverse_Term
  }.

  Instance Traverse_Value_Guard : Traverse Value Guard :=
  {
    traverse := traverse_Guard
  }.

  Instance TraverseVarInjective_Value : @TraverseVarInjective Value _ Value _.
  Proof.
    constructor; prove_traverse_var_injective.
  Qed.

  Lemma traverse_Guards_injective : forall (l1 l2 : list Guard) f n,
    List.map (traverse_Guard (fun l x : nat => ValueVar (f l x)) n) l1 =
    List.map (traverse_Guard (fun l x : nat => ValueVar (f l x)) n) l2 ->
    (forall x1 x2 l : nat, f l x1 = f l x2 -> x1 = x2) ->
    (forall f : nat -> nat -> nat,
    (forall x1 x2 l : nat, f l x1 = f l x2 -> x1 = x2) ->
    forall (t1 t2 : Guard) (l : nat),
    traverse_var f l t1 = traverse_var f l t2 -> t1 = t2) ->
    l1 = l2.
  Proof.
    induction l1, l2; intros * MapInj ? TravInj; try (reflexivity || discriminate).
    injection MapInj; intros ? Inj.
    apply TravInj in Inj; subst; try (f_equal; eapply IHl1); eassumption.
  Qed.

  Ltac prove_traverse_var_injective :=
    let t1 := fresh "t1" in
    intros ? ? t1; induction t1;
    let t2 := fresh "t2" in
    intro t2; destruct t2; simpl;
    let h := fresh "h" in
    intros ? h; inversion h;
    f_equal;
    eauto using @traverse_var_injective with typeclass_instances.
    (* The lemma [traverse_var_injective] can be useful if the [traverse]
      function at hand calls another [traverse] function which has already
      been proved injective. *)

  Lemma traverse_Value_injective :
    forall f : nat -> nat -> nat,
    (forall x1 x2 l : nat, f l x1 = f l x2 -> x1 = x2) ->
    forall (v1 v2 : Value) (l : nat),
    traverse_var f l v1 = traverse_var f l v2 -> v1 = v2.
  Proof.
    intros until v1. induction v1, v2; intros n InjV;
    inversion InjV; f_equal; try easy;
    eapply H; eassumption.
  Qed.

  Lemma traverse_Term_injective :
    forall (f : nat -> nat -> nat)
    (inj : (forall x1 x2 l : nat, f l x1 = f l x2 -> x1 = x2))
    (t1 t2 : Term) (l : nat),
    traverse_var f l t1 = traverse_var f l t2 -> t1 = t2.
  Proof.
    intros until t1.
    induction t1 using @Term_ind3
      with (PG := fun g1 => forall (g2 : Guard) (l : nat),
        traverse_var f l g1 = traverse_var f l g2 -> g1 = g2);
    intro t2; destruct t2; simpl; intros n Inj; inversion Inj; f_equal;
    try (eapply traverse_Value_injective; eassumption);
    try ((eapply IHt1 || eapply IHt1_1 || eapply IHt1_2); eassumption).
    subst; generalize dependent l.
    induction gs; simpl in *; intros * Eql mTrav.
    - symmetry in mTrav; now apply List.map_eq_nil in mTrav.
    - inversion H; subst.
      symmetry in mTrav; apply List.map_eq_cons in mTrav.
      destruct mTrav as [g' [l' [Eq [Eq2 Eq3]]]]; subst.
      erewrite H3 with (g2 := g').
      * f_equal; apply IHgs; eauto.
        f_equal; eauto.
      * eauto.
  Qed.

  Instance TraverseVarInjective_Term : @TraverseVarInjective Value _ Term _.
  Proof. constructor; apply traverse_Term_injective. Qed.

  Lemma traverse_Value_functorial : forall f g (v : Value) l,
    traverse g l (traverse f l v) = traverse (fun l x => traverse g l (f l x)) l v.
  Proof.
    prove_traverse_functorial.
  Qed.

  Lemma traverse_Term_functorial : forall f g (t : Term) l,
    traverse g l (traverse f l t) = traverse (fun l x => traverse g l (f l x)) l t.
  Proof.
    intros until t.
    induction t using @Term_ind3
      with (PG := fun g1 => forall (l : nat),
      traverse g l (traverse f l g1) = traverse (fun l x => traverse g l (f l x)) l g1);
    intros l; simpl; f_equal; try (apply traverse_Value_functorial);
    try (apply IHt || apply IHt1 || apply IHt2).
    induction gs; simpl in *.
    - reflexivity.
    - inversion H as [| ? ? Eq]. subst. rewrite IHgs.
      * now rewrite Eq.
      * assumption.
  Qed.

  Instance TraverseFunctorial_Value : @TraverseFunctorial Value _ Value _.
  Proof. constructor; apply traverse_Value_functorial. Qed.

  Instance TraverseFunctorial_Term : @TraverseFunctorial Value _ Term _.
  Proof. constructor; apply traverse_Term_functorial. Qed.

  Instance TraverseIdentifiesVar_Value : TraverseIdentifiesVar.
  Proof. constructor; prove_traverse_identifies_var. Qed.

  Lemma traverse_Value_relative :
    forall (f g : nat -> nat -> Value) (p : nat) (v : Value) (m l : nat),
    (forall l' x : nat, f (l' + p) x = g l' x) ->
    m = l + p -> traverse f m v = traverse g l v.
  Proof.
    intros * Eq natEq.
    destruct v; simpl; try easy.
    rewrite natEq; apply Eq.
  Qed.

  Lemma traverse_Term_relative :
    forall (f g : nat -> nat -> Value) (p : nat) (t : Term) (m l : nat),
    (forall l' x : nat, f (l' + p) x = g l' x) ->
    m = l + p -> traverse f m t = traverse g l t.
  Proof.
    intros until t.
    induction t using @Term_ind3
      with (PG := fun g1 => forall (m l : nat),
      (forall l' x : nat, f (l' + p) x = g l' x) ->
      m = l + p -> traverse f m g1 = traverse g l g1);
    intros * Eq natEq; simpl; f_equal;
    try (eapply traverse_Value_relative; eassumption);
    try (apply IHt1 || apply IHt2 || apply IHt); try (assumption || lia).
    induction gs.
    - reflexivity.
    - inversion H as [| ? ? EqInd]; subst; simpl in *.
      erewrite EqInd.
      + f_equal; apply IHgs; assumption.
      + assumption.
      + lia.
  Qed.

  Instance TraverseRelative_Value : @TraverseRelative Value Value _.
  Proof. constructor; apply traverse_Value_relative. Qed.

  Instance TraverseRelative_Term : @TraverseRelative Value Term _.
  Proof. constructor; apply traverse_Term_relative. Qed.

  Lemma traverse_Value_identity:
    forall f,
    (forall l x, f l x = var x) ->
    forall (v : Value) l,
    traverse f l v = v.
  Proof.
    intros; destruct v; simpl; try reflexivity; now rewrite H.
  Qed.

  Lemma traverse_Term_identity:
    forall f,
    (forall l x, f l x = var x) ->
    forall (t : Term) l,
    traverse f l t = t.
  Proof.
    intros until t.
    induction t as [| | | | | | ? ? ? Fs | | | ] using @Term_ind3
      with (PG := fun g1 => forall (l : nat), traverse f l g1 = g1);
    intros; simpl; f_equal;
    try (eapply traverse_Value_identity; eassumption);
    try (apply IHt1 || apply IHt2 || apply IHt); try (assumption || lia).
    induction gs.
    - reflexivity.
    - simpl in *. inversion Fs as [| ? ? EqInd]; subst.
      rewrite EqInd; f_equal; apply IHgs; assumption.
  Qed.

  Instance TraverseVarIsIdentity_Value : @TraverseVarIsIdentity Value _ Value _.
  Proof. constructor; apply traverse_Value_identity. Qed.

  Instance TraverseVarIsIdentity_Term : @TraverseVarIsIdentity Value _ Term _.
  Proof. constructor; apply traverse_Term_identity. Qed.

  (* First argument: Value *)
  (* Second argument: Variable *)
  (* Third argument: Term *)
  Type @subst Value Term.


  (*Lemma EmptyEnv_app_cons : forall env1 env2 T, ~ EmptyEnv (env1 ++ Some T :: env2).*)
  (*Proof.*)
  (*  induction env1; intros.*)
  (*  - intros E; inversion E; subst; discriminate.*)
  (*  - destruct a; intros E; inversion E; subst.*)
  (*    + discriminate.*)
  (*    + now apply IHenv1 in H2.*)
  (*Qed.*)

  (*Lemma SingletonEnv_app_cons : forall env1 env2 T,*)
  (*  SingletonEnv (env1 ++ Some T :: env2) ->*)
  (*  EmptyEnv env1 /\ EmptyEnv env2.*)
  (*Proof.*)
  (*  induction env1; intros.*)
  (*  - repeat constructor; assumption.*)
  (*  - simpl in *. destruct a.*)
  (*    + now apply EmptyEnv_app_cons in H.*)
  (*    + apply IHenv1 in H; destruct H.*)
  (*      repeat constructor; assumption.*)
  (*Qed.*)

  (*Lemma lookup_app_cons_weak : forall v env1 env2 T1 T2,*)
  (*  lookup v (None :: env1 ++ Some T1 :: env2) = Some T2 ->*)
  (*  lookup (v - 1) (env1 ++ Some T1 :: env2) = Some T2.*)
  (*Proof.*)
  (*  induction v; intros; simpl in *.*)
  (*  - discriminate.*)
  (*  - now rewrite PeanoNat.Nat.sub_0_r.*)
  (*Qed.*)

  (*Lemma SingletonEnv_lookup_Some : forall env1 env2 T1 T2 v,*)
  (*  lookup v (env1 ++ Some T1 :: env2) = Some T2 ->*)
  (*  SingletonEnv (env1 ++ Some T1 :: env2) ->*)
  (*  T1 = T2.*)
  (*Proof.*)
  (*  induction env1; intros.*)
  (*  - simpl in *.*)
  (*    destruct v.*)
  (*    + now inversion H.*)
  (*    + simpl in *.*)
  (*      apply EmptyEnv_lookup with (x := v) in H0.*)
  (*      rewrite H in H0; discriminate.*)
  (*  - simpl in *.*)
  (*    destruct a; simpl in *.*)
  (*    + now apply EmptyEnv_app_cons in H0.*)
  (*    + eapply IHenv1 with (v := v - 1) (env2 := env2).*)
  (*      * now apply lookup_app_cons_weak.*)
  (*      * assumption.*)
  (*Qed.*)

  (*Lemma insert_Empty_eq : forall x y T1 T2 env,*)
  (*  insert x T1 Empty = insert y T2 env ->*)
  (*  x = y /\ T1 = T2 /\ env = Empty.*)
  (*Proof.*)
  (*  rewrite Empty_nil.*)
  (*  induction x; destruct y; intros.*)
  (*  - rewrite raw_insert_zero in H.*)
  (*    rewrite raw_insert_zero in H.*)
  (*    inversion H.*)
  (*    intuition.*)
  (*  - rewrite raw_insert_zero in H.*)
  (*    rewrite raw_insert_successor in H.*)
  (*    inversion H.*)
  (*    symmetry in H2.*)
  (*    now apply insert_nil in H2.*)
  (*  - rewrite raw_insert_zero in H.*)
  (*    rewrite raw_insert_successor in H.*)
  (*    inversion H.*)
  (*  - destruct env.*)
  (*    + rewrite raw_insert_successor in H; rewrite raw_insert_successor in H.*)
  (*      inversion H; cbv in H1. simpl in H1. subst.*)
  (*    inversion H.*)

  Lemma EnvironmentSubtype_create_EmptyEnv : forall env1 env2,
    env1 ≤ₑ env2 ->
    create_EmptyEnv env1 ≤ₑ create_EmptyEnv env2.
  Proof.
    intros.
  Admitted.

  Lemma weak_Bool_1 : forall p env b T,
    WellTypedTerm p env (TValue (ValueBool b)) T ->
    WellTypedTerm p (create_EmptyEnv env) (TValue (ValueBool b)) T.
  Proof.
    intros * WT.
    remember (TValue (ValueBool b)) as V.
    revert HeqV.
    induction WT; intro; try discriminate.
    - constructor; apply create_EmptyEnv_EmptyEnv.
    - constructor; apply create_EmptyEnv_EmptyEnv.
    - subst.
      generalize (IHWT eq_refl).
      intros.
      eapply SUB with (env2 := create_EmptyEnv env2);
      try eassumption.
      now apply EnvironmentSubtype_create_EmptyEnv.
  Qed.

  Lemma weak_Bool_2 : forall p env b T,
    WellTypedTerm p env (TValue (ValueBool b)) T ->
    env ≤ₑ create_EmptyEnv env.
  Proof.
    intros * WT.
    remember (TValue (ValueBool b)) as V.
    revert HeqV.
    induction WT; intro; try discriminate; try apply EnvironmentSubtype_refl.
    - admit. (* Need one more lemma *)
    - admit. (* Need one more lemma *)
    - subst.
      eapply EnvSubtypeTrans.
      eassumption.
      generalize (IHWT eq_refl); intros Sub'.
      apply EnvironmentSubtype_length in H.
      apply create_EmptyEnv_length in H.
      now rewrite H.
  Admitted.

  Lemma canonical_form_BTBool : forall p env b T,
    WellTypedTerm p env (TValue (ValueBool b)) T ->
    T = TUBase BTBool.
  Proof.
    intros * WT.
    remember (TValue (ValueBool b)) as V.
    revert HeqV.
    induction WT; intros; try discriminate;
    try reflexivity.
    subst.
    generalize (IHWT eq_refl); intros ->.
    inversion H0; now subst.
  Qed.

  Lemma canonical_form_BTUnit : forall p env T,
    WellTypedTerm p env (TValue ValueUnit) T ->
    T = TUBase BTUnit.
  Proof.
    intros * WT.
    remember (TValue ValueUnit) as V.
    revert HeqV.
    induction WT; intros; subst; try discriminate.
    reflexivity.
    generalize (IHWT eq_refl); intros ->.
    inversion H0; now subst.
  Qed.

  Lemma weakening_Bool : forall p env b,
    WellTypedTerm p env (TValue (ValueBool b)) (TUBase BTBool) ->
    forall T',
    Unrestricted T' ->
    WellTypedTerm p (Some T' :: env) (TValue (ValueBool b)) (TUBase BTBool).
  Proof.
    intros * WT.
    remember (TValue (ValueBool b)) as V.
    remember (TUBase BTBool) as T.
    induction WT; intros; subst; try discriminate.
    - eapply SUB with (env2 := None :: env).
      + constructor. assumption. apply EnvironmentSubtype_refl.
      + apply Subtype_refl.
      + now repeat constructor.
    - eapply SUB with (env2 := None :: env).
      + constructor. assumption. apply EnvironmentSubtype_refl.
      + apply Subtype_refl.
      + now repeat constructor.
    - inversion H0; subst.
      eapply SUB with (env2 := Some T' :: env2).
      + constructor. apply Subtype_refl. assumption.
      + apply Subtype_refl.
      + apply IHWT; (reflexivity || assumption).
  Qed.

  Lemma weakening_Unit : forall p env,
    WellTypedTerm p env (TValue ValueUnit) (TUBase BTUnit) ->
    forall T',
    Unrestricted T' ->
    WellTypedTerm p (Some T' :: env) (TValue ValueUnit) (TUBase BTUnit).
  Proof.
    intros * WT.
    remember (TValue ValueUnit) as V.
    remember (TUBase BTUnit) as T.
    induction WT; intros; subst; try discriminate.
    - eapply SUB with (env2 := None :: env).
      + constructor. assumption. apply EnvironmentSubtype_refl.
      + apply Subtype_refl.
      + now repeat constructor.
    - inversion H0; subst.
      eapply SUB with (env2 := Some T' :: env2).
      + constructor. apply Subtype_refl. assumption.
      + apply Subtype_refl.
      + apply IHWT; (reflexivity || assumption).
  Qed.

  Lemma weakening_Value : forall p env v T,
    WellTypedTerm p env (TValue v) T ->
    forall T',
    Unrestricted T' ->
    WellTypedTerm p (Some T' :: env) (shift 0 (TValue v)) T.
  Proof.
    intros * WT.
    remember (TValue v) as V.
    revert HeqV.
    induction WT; intros; try discriminate.
    - simpl_lift_goal; simpl; simpl_lift_goal; simpl.
      eapply SUB with (env2 := None :: env).
      + constructor. assumption. apply EnvironmentSubtype_refl.
      + apply Subtype_refl.
      + constructor; assumption.
    - simpl_lift_goal; simpl; simpl_lift_goal; simpl.
      eapply SUB with (env2 := None :: env).
      + constructor. assumption. apply EnvironmentSubtype_refl.
      + apply Subtype_refl.
      + now repeat constructor.
    - simpl_lift_goal; simpl; simpl_lift_goal; simpl.
      eapply SUB with (env2 := None :: env).
      + constructor. assumption. apply EnvironmentSubtype_refl.
      + apply Subtype_refl.
      + now repeat constructor.
    - simpl_lift_goal; simpl; simpl_lift_goal; simpl.
      eapply SUB with (env2 := None :: env).
      + constructor. assumption. apply EnvironmentSubtype_refl.
      + apply Subtype_refl.
      + now repeat constructor.
    - subst.
      eapply SUB with (env2 := Some T' :: env2).
      + constructor. apply Subtype_refl. assumption.
      + eassumption.
      + now apply IHWT.
  Qed.

  Lemma weakening_Term : forall p env t T,
    WellTypedTerm p env t T ->
    forall T',
    Unrestricted T' ->
    WellTypedTerm p (Some T' :: env) (shift 0 t) T.
  Proof.
    intros * WT.
    induction WT; intros * Unr.
    - apply weakening_Value.
      + now constructor.
      + assumption.
    - apply weakening_Value.
      + now constructor.
      + assumption.
    - apply weakening_Value.
      + now constructor.
      + assumption.
    - apply weakening_Value.
      + now constructor.
      + assumption.
    - simpl_lift_goal; simpl in *.
      destruct v; simpl in *.
      + eapply APP.
        eassumption.
        generalize (canonical_form_BTBool _ _ _ _ WT); intros ->.
        apply weakening_Bool; assumption.
      + eapply APP.
        eassumption.
        generalize (canonical_form_BTUnit _ _ _ WT); intros ->.
        apply weakening_Unit; assumption.
      + generalize (IHWT T' Unr).
        simpl_lift_goal; simpl; simpl_lift_goal; simpl.
        intros WT'.
        eapply APP; eassumption.
    - admit.
    (*- eapply SUB with (env2 := None :: env).*)
    (*  + constructor. assumption. apply EnvironmentSubtype_refl.*)
    (*  + apply Subtype_refl.*)
    (*  + generalize (IHWT1 T' Unr).*)
    (*    generalize (IHWT2 T' Unr).*)
    (*    simpl_lift_goal; simpl; simpl_lift_goal; simpl.*)
    (*    intros WT2' WT1'.*)
    (*    eapply LET with (env1 := None :: env1) (env2 := None :: env2).*)
    (*    * constructor. assumption.*)
    (*    * apply WT1'.*)
    - generalize (IHWT T' Unr).
      simpl_lift_goal; simpl; simpl_lift_goal; simpl.
      intros WT'.
      eapply SUB with (env2 := None :: ⌈ env ⌉ₑ).
      + constructor. assumption. apply EnvironmentSubtype_refl.
      + apply Subtype_refl.
      + assert (H : None :: ⌈ env ⌉ₑ = ⌈ None :: env ⌉ₑ). admit.
        rewrite H.
        eapply SPAWN.
  Admitted.

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

  Lemma EnvironmentSubtype_middle : forall env1_1 env1_2 env2 A,
    env1_1 ++ Some A :: env1_2 ≤ₑ env2 ->
    exists env2_1 env2_2,
    (env2 = env2_1 ++ None :: env2_2) \/
    exists A', (env2 = env2_1 ++ Some A' :: env2_2 /\ A ≤ A').
  Proof.
    induction env1_1; simpl; intros * Sub.
    - exists []; simpl.
      remember (Some A :: env1_2) as E.
      revert env1_2 A HeqE.
      induction Sub; intros.
      + discriminate.
      + discriminate.
      + inversion HeqE; subst. exists env2. now left.
      + inversion HeqE; subst. exists env2. right. now exists T2.
      + generalize (IHSub1 _ _ HeqE).
        intros [env2_2 [Eq | [A' [Eq Sub]]]].
        * subst. apply EnvironmentSubtype_None_inv in Sub2.
          destruct Sub2 as [env2 Eq Sub].
          exists env2; now left.
        * subst.
          generalize (IHSub2 _ _ eq_refl).
          intros [env2_2' [Eq | [A'' [Eq Sub']]]].
          -- exists env2_2'; now left.
          -- subst. exists env2_2'; right; exists A''; constructor.
             reflexivity.
             eapply Subtype_trans; eassumption.
      + subst. exists env1_2; right; exists A. constructor.
        reflexivity. apply Subtype_refl.
    - destruct a.
      + apply EnvironmentSubtype_Some_inv in Sub.
        destruct Sub as [env2' [[Eq EnvSub] | [T' [Eq [Sub EnvSub]]]]].
        * exists nil, env2'; left. apply Eq.
        * apply IHenv1_1 in EnvSub.
          destruct EnvSub as [env2_1' [env2_2' [Eq' | [A' [Eq' Sub']]]]];
          subst; exists (Some T' :: env2_1'), env2_2'.
          -- now left.
          -- right; now exists A'.
      + apply EnvironmentSubtype_None_inv in Sub.
        destruct Sub as [env2' [Eq EnvSub]].
        apply IHenv1_1 in EnvSub.
        destruct EnvSub as [env2_1' [env2_2' [Eq' | [A' [Eq' Sub']]]]];
        subst; exists (None :: env2_1'), env2_2'.
        * now left.
        * right; now exists A'.
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

  Lemma EnvironmentSubtype_middle' : forall env1_1 env1_2 env2 A,
    env1_1 ++ Some A :: env1_2 ≤ₑ env2 ->
    exists env2_1 env2_2,
    env1_1 ≤ₑ env2_1 /\ env1_2 ≤ₑ env2_2 /\
    ((env2 = env2_1 ++ None :: env2_2) \/
    exists A', (env2 = env2_1 ++ Some A' :: env2_2 /\ A ≤ A')).
  Proof.
    induction env1_1; simpl; intros * Sub.
    - apply EnvironmentSubtype_Some_inv in Sub.
      destruct Sub as [env2' [[Eq EnvSub] | [T' [Eq1 [Sub EnvSub]]]]].
      + exists [], env2'.
        do 2 constructor. assumption.
        now left.
      + exists [], env2'.
        do 2 constructor. assumption.
        right; now exists T'.
    - destruct a.
      + simpl_SubEnv; subst.
        * apply IHenv1_1 in EnvSub.
          destruct EnvSub as [env2_1 [env2_2 [Sub1 [Sub2 [Eq' | [A' [Eq' Sub']]]]]]];
          subst; exists (None :: env2_1), env2_2; repeat split;
          try assumption;
          try (now left ||
               apply EnvSubtypeTrans with (env2 := Some T :: env2_1);
               constructor; try assumption; apply EnvSubtypeRefl).
          right; now exists A'.
        * apply IHenv1_1 in EnvSub.
          destruct EnvSub as [env2_1 [env2_2 [Sub1 [Sub2 [Eq' | [A' [Eq' Sub']]]]]]];
          subst; exists (Some T :: env2_1), env2_2; repeat split;
          try assumption;
          try (constructor; try assumption; fail);
          try now left.
          right; now exists A'.
      + simpl_SubEnv; subst.
        apply IHenv1_1 in Sub0.
        destruct Sub0 as [env2_1 [env2_2 [Sub1 [Sub2 [Eq' | [A' [Eq' Sub']]]]]]].
        * subst; exists (None :: env2_1), env2_2; repeat split.
          -- now constructor.
          -- assumption.
          -- now left.
        * subst; exists (None :: env2_1), env2_2; repeat split.
          -- now constructor.
          -- assumption.
          -- right. now exists A'.
  Qed.

  Lemma subst_lemma_TValue : forall p env1_1 env1_2 A B v1,
    WellTypedTerm p (env1_1 ++ Some A :: env1_2) (TValue v1) B ->
    forall v2 env2 A' env,
    WellTypedTerm p env2 (TValue v2) A' ->
    A' ≤ A ->
    (env1_1 ++ None :: env1_2) +ₑ env2 ~= env ->
    WellTypedTerm p env (subst v2 (length env1_1) (TValue v1)) B.
  Proof.
    intros * WT1.
    remember (env1_1 ++ Some A :: env1_2) as E.
    remember (TValue v1) as V.
    generalize dependent A.
    induction WT1; intros * Eq * WT2 Sub Dis; subst; try discriminate.
    - simpl_subst_goal. simpl. simpl_lift_goal. simpl.
      assert (Heq : T = A). admit.
      assert (Hv : v = length env1_1). admit.
      subst.
      simpl_subst_goal. admit.
    - admit. (* use exfalso *)
    - admit. (* use exfalso *)
    - admit. (* use exfalso *)
    - apply EnvironmentSubtype_middle in H.
      destruct H as [env2_1 [env2_2 [Eq | [A'' [Eq Sub']]]]].
      + subst.
        eapply SUB.
        apply EnvSubtypeRefl.
        eassumption.
        eapply IHWT1.
        * reflexivity.
        * admit.
        * apply WT2.
        * eassumption.
        * assumption.
      + subst.
        eapply SUB.
        apply EnvSubtypeRefl.
        eassumption.
        eapply IHWT1.
        * reflexivity.
        * admit.
        * eassumption.
        * eassumption.
        * assumption.
  Admitted.

(**
    We follow the method of Stark's Thesis 'Mechanising Syntax with Binders
    in Coq'.

    A de Bruijn substitution can be seen as a function sigma : nat -> Term.
    A more specific subclass are renamings, that replace in index with other
    indices, represented by a function xi : nat -> nat.

    We first define the renaming primitives.
  *)

  (** The identity renaming just returns its argument *)
  Definition id {X} (x : X) := x.

  (** Shifting is a renaming that increments a variable by one *)
  Definition shift := S.

  (** Extension extends a substitution sigma : nat -> Term with a new element *)
  Definition extend {X : Type} (x : X) (xi : nat -> X) :=
    fun n => match n with
             | 0 => x
             | S n => xi n
             end.

  (** We define the lifting of renaming *)
  Definition lift_renaming (xi : nat -> nat) : nat -> nat :=
    (extend 0 (xi >> shift)).

  Definition rename_Value (xi : nat -> nat) (v : Value) : Value :=
    match v with
    | ValueVar (Var n) => (ValueVar (Var (xi n)))
    | _ => v
    end.

  Definition lift_Value (sigma : nat -> Value) : nat -> Value :=
    extend (ValueVar (Var 0)) (sigma >> (rename_Value shift)).

  Definition subst_Value (sigma_term : nat -> Value) (v : Value) : Value :=
    match v with
    | ValueVar (Var x) => sigma_term x
    | v => v
    end.

  Fixpoint subst_Term (sigma : nat -> Value) (t : Term) : Term :=
    match t with
    | TValue v => TValue (subst_Value sigma v)
    | TLet t1 t2  => TLet (subst_Term sigma t1) (subst_Term (lift_Value sigma) t2)
    | TApp def v => TApp def (subst_Value sigma v)
    | TSpawn t1 => TSpawn (subst_Term sigma t1)
    | TNew => TNew
    | TSend v m v' => TSend (subst_Value sigma v) m (subst_Value sigma v')
    | TGuard v e guards => TGuard (subst_Value sigma v) e (map (subst_Guard sigma) guards)
    end
  with subst_Guard (sigma : nat -> Value) (g : Guard) : Guard :=
    match g with
    | GFail => GFail
    | GFree t1 => GFree (subst_Term sigma t1)
    (* We lift sigma twice, because a receive introduces 2 new variables *)
    | GReceive m t1 => GReceive m (subst_Term (lift_Value (lift_Value sigma)) t1)
    end.

  Definition nVar n := ValueVar (Var n).

  Definition subst_1 (t : Term) (v : Value) : Term :=
    subst_Term (extend v nVar) t.

  Notation "s .: sigma" := (extend s sigma) (at level 70).
  Notation "s [ sigma ]" := (subst_Term sigma s) (at level 7, left associativity, format "s '/' [ sigma ]").
  Notation "s '..'" := (extend s nVar) (at level 1, format "s ..").

  Definition subst_tTest (t : Term) (v : Value) : Term :=
    t[v..].

  (*Compute (subst_1 (TValue (ValueVar (Var 0))) ValueUnit ).*)
  (*Compute ((TValue (ValueVar (Var 0)))[ValueUnit..]).*)

  Lemma subst_1_Var_0 : forall v, subst_1 (TValue (ValueVar (Var 0))) v = TValue v.
  Proof.
    destruct v; unfold subst_1; reflexivity.
  Qed.

  Lemma subst_id_left : forall {T U} (f : T -> U), id >> f = f.
  Proof.
    intros; reflexivity.
  Qed.

  Lemma subst_id_right : forall {T U} (f : T -> U), f = id >> f.
  Proof.
    intros; reflexivity.
  Qed.

  Lemma extend_distr : forall {T U} (s : T) (sigma : nat -> T) (f : T -> U),
    (extend s sigma) >> f = extend (f s) (sigma >> f).
  Proof.
    (* Extensionality is required to prove this *)
    intros; extensionality x; now destruct x.
  Qed.

  Lemma interaction : forall {T} (s : T) (sigma : nat -> T),
    shift >> (extend s sigma) = sigma.
  Proof.
    reflexivity.
  Qed.

  Lemma eta_id : extend 0 shift = id.
  Proof.
    (* Extensionality is required to prove this *)
    intros; extensionality x; now destruct x.
  Qed.

  Lemma eta_extend : forall {T} (sigma : nat -> T),
    extend (sigma 0) (shift >> sigma) = sigma.
  Proof.
    (* Extensionality is required to prove this *)
    intros; extensionality x; now destruct x.
  Qed.

  Lemma lift_Value_id : lift_Value nVar = nVar.
  Proof.
    extensionality x.
    intros; now destruct x.
  Qed.

  Lemma subst_Value_id : forall v, subst_Value nVar v = v.
  Proof.
    destruct v; try reflexivity; now destruct v.
  Qed.

  Lemma subst_id: forall t,
    subst_Term nVar t = t.
  Proof.
    intros t.
    induction t using @Term_ind2 with (PG := fun g => subst_Guard nVar g = g); simpl;
    try (now repeat rewrite subst_Value_id);
    try (now rewrite IHt).
    - rewrite IHt1; rewrite lift_Value_id; now rewrite IHt2.
    - induction gs as [| g gs]; rewrite subst_Value_id.
      + reflexivity.
      + inversion H as [| ? ? Eq F]; subst.
        apply IHgs in F; injection F.
        simpl; intros -> ?; now rewrite Eq.
    - repeat rewrite lift_Value_id; now rewrite IHt.
  Qed.

  Lemma In_Some_EmptyEnv : forall env x, In (Some x) env -> ~ EmptyEnv env.
  Proof.
    intros * In; induction env.
    - inversion In.
    - destruct a; simpl in *; intros Empty.
      + inversion Empty; subst; discriminate.
      + destruct In.
        * discriminate.
        * inversion Empty; subst; now apply IHenv.
  Qed.

  Lemma subst_lemma_TValue : forall p env1 env2 env A A' B v1 v2,
    (*lookup x env1 = (Some A) ->*)
    WellTypedTerm p (Some A :: env1) (TValue v1) B ->
    WellTypedTerm p env2 (TValue v2) A' ->
    A' ≤ A ->
    env1 +ₑ env2 ~= env ->
    WellTypedTerm p env (subst_1 (TValue v1) v2) B.
  Proof.


  Lemma subst_lemma_TValue : forall p env1 env2 env A A' B v1 v2,
    (*lookup x env1 = (Some A) ->*)
    WellTypedTerm p (Some A :: env1) (TValue v1) B ->
    WellTypedTerm p env2 (TValue v2) A' ->
    A' ≤ A ->
    env1 +ₑ env2 ~= env ->
    WellTypedTerm p env (subst_1 (TValue v1) v2) B.
  Proof.
    intros * WT1.
    remember (TValue v1) as V.
    remember (Some A :: env1) as E.
    revert HeqV HeqE v2 A' env2 env.
    induction WT1; intros Eq1 Eq2 * WT2 Sub Dis; try discriminate.
    + simpl. admit.
    + subst. simpl. inversion H; subst. discriminate.
    + subst. simpl. inversion H; subst. discriminate.
    + subst. simpl. inversion H; subst. discriminate.
    + subst.
      inversion H; subst.
      * admit.
      * 
      eapply SUB.
      * apply EnvSubtypeRefl.
      * apply H0.
      * eapply IHWT1.
        -- reflexivity.
        -- admit.
        -- apply WT2.
        -- apply Sub.
        -- 

    destruct v1.
    + inversion

  Lemma sub_lemma : forall p env1 env2 env A A' B v t,
    (*In (Some A) env1 ->*)
    WellTypedTerm p (Some A :: env1) t B ->
    WellTypedTerm p env2 (TValue v) A' ->
    A' ≤ A ->
    env1 +ₑ env2 ~= env ->
    WellTypedTerm p env (subst_1 t v) B.
  Proof.
    intros * In WT1.
    (*remember env1 as env1' eqn: E.*)
    revert In.
    induction WT1 using @WellTypedTerm_ind3 with
      (P0 := fun _ _ _ _ => True)
      (P1 := fun _ _ _ _ => True).
    - intros In WT2 Sub Dis.
      simpl. admit.
    - intros. admit. (* not possible *)
    - intros. admit. (* not possible *)
    - intros. admit. (* not possible *)
    - intros. simpl.

    revert env2 env v A'.
    remember (Some A :: env1) as env1' eqn:E.
    generalize dependent A.
    generalize dependent env1.
    induction WT1; intros.
    - simpl in *.
      assert (zero : v = 0). admit.
      assert (SubTy : T = A). admit.
      subst. simpl.
      (*rewrite subst_1_Var_0.*)
      eapply SUB with (env2 := env2).
      (* env1 is empty, thus env2 = env *)
      admit.
      apply H2.
      apply H1.
    - inversion H; subst; discriminate.
    - inversion H; subst; discriminate.
    - inversion H; subst; discriminate.
    - eapply APP.
      + apply H.
      + eapply IHWT1. apply E. apply H0. assumption. assumption.
    - subst.
      inversion H; subst.
      + eapply LET.
        * apply (EnvironmentDis_implies_Comb _ _ _ H2).
        * eapply IHWT1_1.
          -- reflexivity.
          -- apply H0.
          -- assumption.
          -- admit.
    - admit.
    - subst; inversion H; subst; discriminate.
    - admit.
    - admit.
    - subst. inversion H3; subst; inversion H; subst.
      + eapply SUB.
        * apply EnvSubtypeRefl.
        * apply H0.
        * eapply IHWT1.
          -- 
    Admitted.

End subs_def.
