(** * Substitution *)

From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.
From MailboxTypes Require Import TypingRules.
From MailboxTypes Require Import Dblib.DeBruijn.
From MailboxTypes Require Import Dblib.DblibTactics.
From MailboxTypes Require Import Dblib.Environments.

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
  | TLet t1 t2  => TLet (traverse_Term f l t1) (traverse_Term f (1 + l) t2)
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
  (*Type @subst Value Term.*)

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

  Lemma WellTypedTerm_TValue_Un : forall p env v T T',
    WellTypedTerm p env (TValue v) T ->
    T ≤ T' ->
    Unrestricted T' ->
    exists env', EmptyEnv env' /\ env ≤ₑ env'.
  Proof.
    intros * WT.
    remember (TValue v) as V.
    revert T' v HeqV.
    induction WT; intros * Eq Sub Un; subst; try discriminate;
    try (exists env; eauto using EnvironmentSubtype_refl; fail).
    - inversion Eq; subst.
      induction x.
      + rewrite raw_insert_zero.
        exists (None :: env); split.
        constructor; eauto with environment.
        eapply EnvSubtypeTrans with (env2 := Some T' :: env);
        eauto with environment.
      + rewrite raw_insert_successor.
        rewrite lookup_EmptyEnv_None by assumption.
        generalize (IHx eq_refl); intros [env' [Empty' Sub']].
        assert (EmptyTl : EmptyEnv (tl env)).
        {
          induction env; simpl. constructor. now inversion H.
        }
        generalize (EnvironmentSubtype_EmptyEnv_insert_Un (tl env) x T T' Sub Un EmptyTl).
        intros SubE.
        exists (None :: create_EmptyEnv (insert x T (tl env))); split.
        * constructor.
          reflexivity.
          apply create_EmptyEnv_EmptyEnv.
        * now constructor.
    - generalize (IHWT _ _ eq_refl (Subtype_trans _ _ _ H0 Sub) Un).
      intros [env' [Empty' Sub']].
      exists env'; eauto using EnvSubtypeTrans with environment.
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

  Lemma WellTypedTerm_TValue_lookup : forall p x T env,
    WellTypedTerm p env (TValue (ValueVar x)) T ->
    exists T', lookup x env = Some T' /\ T' ≤ T.
  Proof.
    intros * WT.
    apply weak_ValueVar_2 in WT;
    destruct WT as [env' [T' [Sub [Empty [EnvSub WT]]]]].
    apply EnvironmentSubtype_insert_right_inv in EnvSub.
    destruct EnvSub as [env1' [T'' [Sub' ->]]].
    exists T''.
    rewrite lookup_insert_bingo by reflexivity;
    eauto using Subtype_trans.
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

  Lemma EmptyEnv_raw_insert_None : forall x env,
    EmptyEnv env ->
    EmptyEnv (raw_insert x None env).
  Proof.
    induction x; intros * Empty.
    - rewrite raw_insert_zero; now constructor.
    - rewrite raw_insert_successor.
      inversion Empty; subst.
      + rewrite lookup_nil; simpl.
        constructor.
        reflexivity.
        now apply IHx.
      + rewrite lookup_zero; simpl.
        constructor.
        reflexivity.
        now apply IHx.
  Qed.

  Lemma EmptyEnv_raw_insert_None_inv : forall x env,
    EmptyEnv (raw_insert x None env) ->
    EmptyEnv env.
  Proof.
    induction x; intros * Empty.
    - rewrite raw_insert_zero in Empty; now inversion Empty.
    - rewrite raw_insert_successor in Empty.
      inversion Empty; subst.
      destruct env.
      + constructor.
      + rewrite lookup_zero in *; subst.
        constructor.
        reflexivity.
        apply IHx.
        assumption.
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

  Lemma WellTypedTerm_TValue_insert_None_le : forall p env x T v,
    WellTypedTerm p (raw_insert x None env) (TValue (ValueVar v)) T ->
    v < x ->
    WellTypedTerm p env (TValue (ValueVar v)) T.
  Proof.
    intros * WT le.
    apply weak_ValueVar_2 in WT.
    destruct WT as [env' [T'' [Sub'' [Empty [EnvSub WT]]]]].
    generalize (EnvironmentSubtype_raw_insert_insert _ _ _ _ _ Empty EnvSub le).
    intros [env2' [Empty' EnvSub']].
    eapply SUB; try eassumption.
    now constructor.
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

  Lemma WellTypedTerm_TValue_insert_None_eq : forall p env x T,
    ~ WellTypedTerm p (raw_insert x None env) (TValue (ValueVar x)) T.
  Proof.
    intros * WT.
    apply weak_ValueVar_2 in WT.
    destruct WT as [env' [T' [Sub [Empty [EnvSub WT]]]]].
    now apply EnvironmentSubtype_insert_None_Some in EnvSub.
  Qed.

  Lemma WellTypedTerm_TValue_insert_None_gt : forall p env x v T,
    WellTypedTerm p (raw_insert x None env) (TValue (ValueVar v)) T ->
    x < v ->
    WellTypedTerm p env (TValue (ValueVar (v - 1))) T.
  Proof.
    intros * WT Gt.
    generalize (weak_ValueVar_2 _ _ _ _ WT).
    intros [env' [T' [Sub [Empty [EnvSub WT']]]]].
    generalize (EnvironmentSubtype_raw_insert_insert' _ _ _ _ _ Empty EnvSub Gt).
    intros [env2' [Empty' EnvSub']].
    eapply SUB; try eassumption; now constructor.
  Qed.

  (*Lemma weakening: forall p env t T,*)
  (*  WellTypedTerm p env t T ->*)
  (*  forall x v env',*)
  (*  insert x v env = env' ->*)
  (*  WellTypedTerm p env' (shift x t) T.*)
  (*Proof.*)
  (*  intros * WT.*)
  (*  induction WT; intros * Eq; subst.*)
  (*  - simpl_lift_goal. simpl.*)

  Lemma WellTypedTerm_TValue_raw_insert_None : forall p env v x T,
    WellTypedTerm p env (TValue v) T ->
    WellTypedTerm p (raw_insert x None env) (TValue (shift x v)) T.
  Proof.
    intros * WT.
    remember (TValue v) as V.
    revert x v HeqV.
    induction WT; intros; subst; try discriminate;
    try (
      inversion HeqV; subst;
      simpl_lift_goal; simpl;
      constructor;
      now apply EmptyEnv_raw_insert_None
    ).
    - inversion HeqV; subst.
      simpl_lift_goal; simpl.
      destruct (Compare_dec.le_gt_dec x0 x).
      + rewrite lift_idx_old by assumption.
        rewrite insert_insert by assumption.
        apply VAR.
        now apply EmptyEnv_raw_insert_None.
      + destruct x0.
        * inversion g.
        * rewrite <- insert_insert by lia.
          simpl_lift_goal.
          apply VAR.
          now apply EmptyEnv_raw_insert_None.
    - generalize (IHWT x v eq_refl).
      intros WT2.
      eapply SUB; eauto using EnvironmentSubtype_insert.
  Qed.

  (*Lemma WellTypedTerm_raw_insert_None : forall p env t x T,*)
  (*  WellTypedTerm p env t T ->*)
  (*  WellTypedTerm p (raw_insert x None env) (shift x t) T.*)
  (*Admitted.*)

  Lemma subst_insert_TValue_None : forall p env v1 v2 x T,
    WellTypedTerm p (raw_insert x None env) (TValue v1) T ->
    WellTypedTerm p env (subst v2 x (TValue v1)) T.
  Proof.
    intros * WT.
    destruct v1.
    - simpl_subst_goal; simpl; simpl_lift_goal; simpl.
      generalize (canonical_form_BTBool _ _ _ _ WT); intros ->.
      generalize (weak_BTBool_2 _ _ _ _ WT); intros EnvSub.
      apply EnvironmentSubtype_EmptyEnv_insert_None in EnvSub.
      + destruct EnvSub as [env2' [Empty' Sub']].
        eapply SUB; eauto using Subtype_refl.
        destruct b; now constructor.
      + apply create_EmptyEnv_EmptyEnv.
    - simpl_subst_goal; simpl; simpl_lift_goal; simpl.
      generalize (canonical_form_BTUnit _ _ _ WT); intros ->.
      generalize (weak_BTUnit_2 _ _ _ WT); intros EnvSub.
      apply EnvironmentSubtype_EmptyEnv_insert_None in EnvSub.
      + destruct EnvSub as [env2' [Empty' Sub']].
        eapply SUB; eauto using Subtype_refl;
        now constructor.
      + apply create_EmptyEnv_EmptyEnv.
    - simpl_subst_goal; simpl; simpl_lift_goal; simpl.
      unfold subst_idx; dblib_by_cases; simpl.
      + eapply WellTypedTerm_TValue_insert_None_le; eassumption.
      + subst; now apply WellTypedTerm_TValue_insert_None_eq in WT.
      + Search ((?v - 1)).
        now apply WellTypedTerm_TValue_insert_None_gt in WT.
  Qed.

  Lemma subst_TLet : forall t1 t2 v x,
    subst v x (TLet t1 t2) = TLet (subst v x t1) (subst (shift 0 v) (1 + x) t2).
  Proof.
    intros.
    simpl_subst_goal; simpl; simpl_lift_goal.
    f_equal.
    generalize (traverse_relative (fun l x0 : nat => subst_idx (lift l 0 v) (l + x) x0) (fun l x0 : nat => subst_idx (lift l 0 (traverse_Value (fun l' x0' : nat => ValueVar (shift (l' + 0) x0')) 0 v)) (l + S x) x0) 1 t2).
    intros H.
    assert (H1 : forall l y : nat,
      subst_idx (lift (l + 1) 0 v) (l + 1 + x) y =
      subst_idx
      (lift l 0
          (traverse_Value (fun l0 x0 : nat => ValueVar (shift (l0 + 0) x0)) 0 v))
      (l + S x) y
    ).
    {
      intros. simpl_lift_goal. unfold subst_idx. dblib_by_cases; try reflexivity.
      generalize (traverse_functorial (fun l0 x0 : nat => ValueVar (shift (l0 + 0) x0)) (fun l0 x0 : nat => ValueVar (lift l (l0 + 0) x0)) v).
      intros.
      rewrite H0.
      simpl_lift_goal; simpl.
      assert (forall l' x', (fun l0 x0 : nat => ValueVar (lift (l + 1) (l0 + 0) x0)) l' x' = (fun l0 x0 : nat => ValueVar (lift l (l0 + 0) (shift (l0 + 0) x0))) l' x').
      {
        intros. f_equal. repeat rewrite <- plus_n_O.
        symmetry.
        replace (l + 1) with (S l).
        apply lift_lift_fuse_successor.
        rewrite PeanoNat.Nat.add_comm.
        reflexivity.
      }
      generalize (traverse_extensional _ _ _ H1 v 0); eauto.
    }
    generalize (H 1 0 H1 eq_refl); auto.
  Qed.

  Lemma subst_TSpawn : forall v x t,
    subst v x (TSpawn t) = TSpawn (subst v x t).
  Proof.
    intros; now simpl_subst_goal.
  Qed.

  Lemma subst_TSend : forall t1 t2 v x m,
    subst v x (TSend t1 m t2) = TSend (subst v x t1) m (subst v x t2).
  Proof.
    intros; now simpl_subst_goal.
  Qed.

  Lemma subst_GReceive : forall m t v x,
    subst v x (GReceive m t) = GReceive m (subst (lift 2 0 v) (2 + x) t).
  Proof.
    intros.
    simpl_subst_goal; simpl; simpl_lift_goal.
    f_equal.
    generalize (traverse_relative (fun l x0 : nat => subst_idx (lift l 0 v) (l + x) x0) (fun l x0 : nat => subst_idx (lift l 0 (traverse_Value (fun l' x0' : nat => ValueVar (lift 2 (l' + 0) x0')) 0 v)) (l + S (S x)) x0) 2 t).
    intros H.
    apply H; try reflexivity.
    intros l y.
    simpl_lift_goal.
    unfold subst_idx.
    dblib_by_cases; try reflexivity.
    generalize (traverse_functorial (fun l' x0' : nat => ValueVar (lift 2 (l' + 0) x0')) (fun l0 x0 : nat => ValueVar (lift l (l0 + 0) x0)) v 0).
    simpl; intros ->.
    generalize (traverse_relative (fun l0 x0 : nat => ValueVar (lift (l + 2) (l0 + 0) x0)) (fun l0 x0 : nat => ValueVar (lift l (l0 + 0) (lift 2 (l0 + 0) x0))) 0 v).
    intros Eq.
    generalize (Eq 0 0).
    intros Eq'.
    assert (H1 : forall l0 x0 : nat, ValueVar (lift (l + 2) (l0 + 0 + 0) x0) = ValueVar (lift l (l0 + 0) (lift 2 (l0 + 0) x0))).
    {
      intros l' x'; f_equal; repeat rewrite <- plus_n_O.
      destruct (Compare_dec.le_gt_dec l' x') as [L | L].
      - simpl_lift_goal.
        assert (A : lift 2 l' x' = 2 + x') by now simpl_lift_goal.
        rewrite A.
        assert (B : lift l l' (2 + x') = l + 2 + x') by (simpl_lift_goal; lia).
        now rewrite B.
      - rewrite lift_idx_recent by assumption.
        assert (A : lift 2 l' x' = x') by (now rewrite lift_idx_recent).
        rewrite A.
        assert (B : lift l l' x' = x') by (now rewrite lift_idx_recent).
        now rewrite B.
    }
    now apply Eq'.
  Qed.

  Lemma subst_TGuard : forall v1 v2 x e guards,
    subst v1 x (TGuard v2 e guards) = TGuard (subst v1 x v2) e (ListDef.map (subst v1 x) guards).
  Proof.
    intros; simpl_subst_goal; simpl; reflexivity.
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

  Lemma secondEnvironment_insert_inv : forall x T env1 env2,
    ⌈ env1 ⌉ₑ = insert x T ⌈ env2 ⌉ₑ ->
    exists env2' T', env1 = insert x T' env2' /\ T ≤ T' /\ ⌈ env2' ⌉ₑ = ⌈ env2 ⌉ₑ.
  Proof.
    induction x; intros * Eq;
    generalize (secondEnvironment_insert _ _ _ _ Eq);
    intros [Eq1 Eq2].
    - rewrite raw_insert_zero in Eq.
      destruct env1.
      + simpl in *; inversion Eq.
      + simpl in *.
        inversion Eq.
        destruct o.
        * simpl in *.
          destruct T, t; simpl in *.
          (*-- now exists env1.*)
          (*-- discriminate.*)
          (*-- discriminate.*)
          (*-- inversion Eq2; subst.*)
  Admitted.

  (*Lemma secondEnvironment_insert_inv : forall x T env1 env2,*)
  (*  env1 = insert x ⌈ T ⌉ⁿ ⌈ env2 ⌉ₑ ->*)
  (*  env1 = ⌈ env1 ⌉ₑ.*)
  (*Proof.*)
  (*  induction x; intros * Eq.*)
  (*  - rewrite raw_insert_zero in Eq.*)
  (*    destruct env1 as [| e env1].*)
  (*    + reflexivity.*)
  (*    + inversion Eq; subst.*)
  (*      simpl.*)
  (*      rewrite <- secondUsage_idem.*)
  (*      now rewrite <- secondEnvironment_idem.*)
  (*  - destruct env1 as [|e1 env1], env2 as [|e2 env2]; rewrite raw_insert_successor in Eq.*)
  (*    + reflexivity.*)
  (*    + reflexivity.*)
  (*    + simpl in *.*)
  (*      rewrite lookup_nil in Eq.*)
  (*      inversion Eq; simpl; f_equal.*)
  (*      now eapply IHx with (T := T) (env2 := []).*)
  (*    + simpl in *.*)
  (*      rewrite lookup_zero in Eq.*)
  (*      inversion Eq.*)
  (*      destruct e2; simpl in *.*)
  (*      * rewrite <- secondUsage_idem.*)
  (*        f_equal; eapply IHx; reflexivity.*)
  (*      * f_equal; eapply IHx; reflexivity.*)
  (*Qed.*)

  Lemma subst_insert_None : forall p env t1 v x T,
    WellTypedTerm p (raw_insert x None env) t1 T ->
    WellTypedTerm p env (subst v x t1) T.
  Proof.
    intros * WT.
    remember (raw_insert x None env) as E.
    revert x v env HeqE.
    induction WT using @WellTypedTerm_ind3 with
      (P0 := fun env gs T E (WG : WellTypedGuards p env gs T E) =>
        forall v x env',
        env = raw_insert x None env' ->
        WellTypedGuards p env' (List.map (subst v x) gs) T E
      )
      (P1 := fun env g T E (WG : WellTypedGuard p env g T E) =>
        forall v x env',
          env = raw_insert x None env' ->
          WellTypedGuard p env' (subst v x g) T E
      );
    intros; subst;
    try (
      simpl_subst_goal; simpl; simpl_lift_goal;
      constructor;
      eauto using EmptyEnv_raw_insert_None_inv
    ).
    - apply subst_insert_TValue_None.
      rewrite <- HeqE.
      now constructor.
    - simpl_subst_goal; simpl; simpl_lift_goal.
      eapply APP; try eassumption.
      generalize (IHWT _ v0 _ eq_refl).
      simpl_subst_goal; simpl; now simpl_lift_goal.
    - rewrite subst_TLet.
      generalize (EnvironmentCombination_raw_insert_None _ _ _ _ e).
      intros [env1' [env2' [Eq1 [Eq2 [L1 [L2 Comb']]]]]].
      eapply LET with (env1 := env1') (env2 := env2'); eauto.
      apply IHWT2; subst.
      repeat rewrite raw_insert_zero.
      rewrite raw_insert_successor.
      now rewrite lookup_zero.
    - rewrite subst_TSpawn.
      generalize (secondEnvironment_raw_insert_None _ _ _ HeqE).
      intros Eq; rewrite Eq in *.
      apply secondEnvironment_raw_insert_None_inv in HeqE.
      destruct HeqE as [env2'' [Eq1' Eq2']]; subst.
      eapply SPAWN; auto.
    - generalize (EnvironmentDis_raw_insert_None _ _ _ _ e0).
      intros [env1' [env2' [Eq1 [Eq2 [L1 [L2 Comb']]]]]]; subst.
      rewrite subst_TSend.
      eapply SEND; eauto.
      + generalize (IHWT1 x v _ eq_refl).
        simpl_subst_goal; eauto.
      + generalize (IHWT2 x v _ eq_refl).
        simpl_subst_goal; eauto.
    - generalize (EnvironmentDis_raw_insert_None _ _ _ _ e0);
      intros [env1' [env2' [Eq1 [Eq2 [L1 [L2 Comb']]]]]]; subst.
      simpl_subst_goal; simpl.
      eapply GUARD with (env1 := env1') (env2 := env2');
      try (generalize (IHWT x v0 env1' eq_refl); simpl_subst_goal);
      try (generalize (IHWT0 v0 x env2'); simpl_subst_goal); eauto.
    - apply EnvironmentSubtype_raw_insert_None in e.
      destruct e as [env2' [Eq Sub]].
      apply IHWT with (v := v) in Eq.
      eapply SUB; eassumption.
    - generalize (IHWT x v env' eq_refl); eauto.
    - rewrite subst_GReceive.
      eapply RECEIVE; eauto.
      destruct o; eauto.
      right; eauto using BaseEnv_raw_insert_None_inv.
  Qed.

  Lemma subst_Guard_insert_None : forall p env g v x T f,
    WellTypedGuard p (raw_insert x None env) g T f ->
    WellTypedGuard p env (subst v x g) T f.
  Proof.
    intros * WT.
    remember (raw_insert x None env) as E.
    revert x v env HeqE.
    induction WT; intros; subst.
    - simpl_subst_goal; simpl; constructor.
    - simpl_subst_goal; simpl; constructor.
      generalize (subst_insert_None _ _ _ v _ _ H).
      now simpl_subst_goal.
    - rewrite subst_GReceive; econstructor.
      + reflexivity.
      + destruct H0.
        * now left.
        * right. eauto using BaseEnv_raw_insert_None_inv.
      + assert (insert 0 (? e ^^ •) (raw_insert x None env0) = raw_insert (1 + x) None (insert 0 (? e ^^ •) env0)).
        { apply insert_insert; lia. }
        rewrite H in H1.
        rewrite insert_insert in H1 by lia.
        now generalize (subst_insert_None _ _ _ (lift 2 0 v) _ _ H1).
  Qed.

  Lemma subst_Guards_insert_None : forall p env gs v x T f,
    WellTypedGuards p (raw_insert x None env) gs T f ->
    WellTypedGuards p env (List.map (subst v x) gs) T f.
  Proof.
    intros * WT.
    remember (raw_insert x None env) as E.
    revert x v env HeqE.
    induction WT; intros; subst.
    - simpl; constructor; now apply subst_Guard_insert_None.
    - simpl; simpl_subst_goal.
      constructor.
      + generalize (subst_Guard_insert_None _ _ _ v _ _ _ H).
        now simpl_subst_goal.
      + now apply IHWT.
  Qed.

  Lemma subst_lemma_TValue : forall p env1 env2 env A A' B v1 v2 x,
    WellTypedTerm p (insert x A env1) (TValue v1) B ->
    WellTypedTerm p env2 (TValue v2) A' ->
    A' ≤ A ->
    env1 +ₑ env2 ~= env ->
    WellTypedTerm p env (subst v2 x (TValue v1)) B.
  Proof.
    intros * WT1 WT2.
    remember (insert x A env1) as E1.
    remember (TValue v1) as V1.
    remember (TValue v2) as V2.
    revert v1 v2 x A A' env env1 env2 HeqE1 HeqV1 HeqV2 WT2.
    induction WT1; intros; subst; try discriminate.
    - apply insert_EmptyEnv_injective in HeqE1.
      + destruct HeqE1 as [-> [-> Empty]].
        inversion HeqV1; subst.
        simpl_subst_goal; simpl. rewrite lift_zero.
        simpl_subst_goal.
        generalize (EnvDis_EmptyEnv_left env1 env2 env0 Empty H1).
        intros; subst.
        eapply SUB; eauto with environment.
      + assumption.
    - now apply insert_EmptyEnv in H.
    - now apply insert_EmptyEnv in H.
    - now apply insert_EmptyEnv in H.
    - apply EnvironmentSubtype_insert_inv in H;
      destruct H as [env2' [T' [Sub' [EnvSub' [[Eq Un] | Eq]]]]];
      subst.
      + apply subst_insert_TValue_None with (v2 := v2) in WT1.
        eapply WellTypedTerm_TValue_Un in WT2.
        * destruct WT2 as [env'' [Empty'' EnvSub'']].
          generalize (EnvDis_Sub env0 env3 env2' env'' env EnvSub' EnvSub'' H2).
          intros [envE [SubE DisE]].
          generalize (EnvDis_EmptyEnv_right _ _ _ Empty'' DisE); intros ->.
          eapply SUB; eassumption.
        * eapply Subtype_trans with (t2 := A); eassumption.
        * eassumption.
      + generalize (EnvDis_Sub env0 env3 env2' env3 env EnvSub' (EnvironmentSubtype_refl env3) H2).
        intros [env'' [EnvSub'' Dis'']].
        eapply SUB; eauto.
        eapply IHWT1; eauto using Subtype_trans.
  Qed.

  Lemma asdfwe : forall T1 T2,
    ⌈ T1 ⌉ⁿ = T2 -> (exists BT, T2 = TUBase BT) \/ exists E, T2 = (E ^^ ◦).
  Proof.
    intros * Eq; destruct T1; simpl in *; eauto.
  Qed.

  Lemma subst_lemma : forall p env1 env2 env A A' B t v x,
    WellTypedTerm p (insert x A env1) t B ->
    WellTypedTerm p env2 (TValue v) A' ->
    A' ≤ A ->
    env1 +ₑ env2 ~= env ->
    WellTypedTerm p env (subst v x t) B.
  Proof.
    intros * WT1 WT2.
    remember (insert x A env1) as E1.
    revert v x A A' env env1 env2 HeqE1 WT2.
    induction WT1 using @WellTypedTerm_ind3 with
      (P0 := fun env1 gs T E (WG : WellTypedGuards p env1 gs T E) =>
        forall v x A A' env1' env2 env,
        env1 = insert x A env1' ->
        WellTypedTerm p env2 (TValue v) A' ->
        A' ≤ A ->
        env1' +ₑ env2 ~= env ->
        WellTypedGuards p env (List.map (subst v x) gs) T E
      )
      (P1 := fun env1 g T E (WG : WellTypedGuard p env1 g T E) =>
        forall v x A A' env1' env2 env,
          env1 = insert x A env1' ->
          WellTypedTerm p env2 (TValue v) A' ->
          A' ≤ A ->
          env1' +ₑ env2 ~= env ->
          WellTypedGuard p env (subst v x g) T E
      );
    intros; subst; try discriminate;
    try (now apply insert_EmptyEnv in e).
    (*induction WT1; intros; subst; try discriminate.*)
    - eapply subst_lemma_TValue; try eassumption.
      apply insert_EmptyEnv_injective in HeqE1.
      + destruct HeqE1 as [-> [-> Empty]].
        now constructor.
      + assumption.
    - simpl_subst_goal; simpl; simpl_lift_goal; simpl.
      eapply APP.
      eassumption.
      generalize (IHWT1 _ _ _ _ _ _ _ eq_refl WT2 H H0).
      now simpl_subst_goal.
    - rewrite subst_TLet.
      generalize (EnvironmentCombination_insert _ _ _ _ _ e).
      intros [env1' [env2' [L1 [L2 [Comb2 [[Eq1 Eq2] | [[Eq1 Eq2] | [T1' [T2' [Eq1 [Eq2 TComb]]]]]]]]]]];
      subst.
      (* x is in the left term *)
      + apply EnvironmentDis_Comb_comm in H0.
        generalize (EnvironmentDis_Comb env4 env1' env2' env3 env0 H0 Comb2).
        intros [envT [CombT DisT]].
        eapply LET with (env1 := envT) (env2 := env2').
        * assumption.
        * eapply IHWT1_1; try eauto using EnvironmentDis_Comb_comm.
        * apply subst_insert_None.
          rewrite raw_insert_successor.
          repeat rewrite raw_insert_zero.
          rewrite lookup_zero.
          simpl.
          now rewrite raw_insert_zero in WT1_2.
      (* x is in the right term *)
      + generalize (EnvironmentDis_Comb_rev _ _ _ _ _ H0 Comb2).
        intros [envT [CombT DisT]].
        eapply LET with (env1 := env1') (env2 := envT) (T1 := T1).
        * assumption.
        * now apply subst_insert_None.
        * apply WellTypedTerm_TValue_raw_insert_None with (x := 0) in WT2.
          rewrite raw_insert_zero in *.
          assert (Eq : Some ⌊ T1 ⌋ :: insert x A env2' = insert (S x) A (Some ⌊ T1 ⌋ :: env2'));
          eauto using raw_insert_successor.
          assert (DisE : Some ⌊ T1 ⌋ :: env2' +ₑ None :: env4 ~= Some ⌊ T1 ⌋ :: envT); eauto with environment.
      (* x is in both terms *)
      + generalize (EnvironmentDis_Comb_rev _ _ _ _ _ H0 Comb2).
        intros [envT2 [CombT2 DisT2]].
        apply EnvironmentDis_Comb_comm in H0.
        generalize (EnvironmentDis_Comb _ _ _ _ _ H0 Comb2).
        intros [envT1 [CombT1 DisT1]].
        eapply LET with (env1 := envT1) (env2 := envT2) (T1 := T1).
        * admit. (* This should work *)
        * admit.
        * apply WellTypedTerm_TValue_raw_insert_None with (x := 0) in WT2.
          rewrite raw_insert_zero in *.
          assert (Eq : Some ⌊ T1 ⌋ :: insert x A env2' = insert (S x) A (Some ⌊ T1 ⌋ :: env2'));
          eauto using raw_insert_successor.
          assert (DisE : Some ⌊ T1 ⌋ :: env2' +ₑ None :: env4 ~= Some ⌊ T1 ⌋ :: envT2); eauto with environment.
          eapply IHWT1_2 with (env1 := Some ⌊ T1 ⌋ :: env2').
          -- rewrite raw_insert_successor.
             rewrite lookup_zero.
             reflexivity.
          -- apply WT2.
          -- admit.
          -- assumption.
    - rewrite subst_TSpawn. admit.
    - rewrite subst_TSend.
      generalize (EnvironmentDisCombination_insert _ _ _ _ _ e0).
      intros [env1' [env2' [L1 [L2 [Dis' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT [Eq1 Eq2]]]]]]]]];
      subst.
      (* x in the left term *)
      + subst.
        apply EnvironmentDis_Comb_comm in H0.
        generalize (EnvironmentDis_assoc env4 env1' env2' env3 env0 H0 Dis').
        intros [envT [DisT1 DisT2]].
        eapply SEND with (env1 := envT) (env2 := env2').
        apply EnvironmentDis_Comb_comm in DisT2.
        * generalize (subst_lemma_TValue _ _ _ envT _ _ _ _ _ _ WT1_1 WT2 H DisT2).
          now simpl_subst_goal.
        * reflexivity.
        * assumption.
        * eapply subst_insert_None with (v := v) in WT1_2.
          generalize WT1_2; now simpl_subst_goal.
      (* x in the right term *)
      + subst.
        generalize (EnvironmentDis_assoc_rev _ _ _ _ _ H0 Dis').
        intros [envT [DisT1 DisT2]].
        eapply SEND with (env1 := env1') (env2 := envT).
        * eapply subst_insert_None with (v := v) in WT1_1.
          generalize WT1_1; now simpl_subst_goal.
        * reflexivity.
        * assumption.
        * apply EnvironmentDis_Comb_comm in DisT2.
          generalize (subst_lemma_TValue _ _ _ envT _ _ _ _ _ _ WT1_2 WT2 H DisT2).
          now simpl_subst_goal.
      (* x in the both terms *)
      + subst.
        generalize (EnvironmentDisCombination_insert_Type_eq _ _ _ _ _ _ e0);
        intros; subst.
        generalize (EnvironmentDis_assoc_rev _ _ _ _ _ H0 Dis').
        intros [envT2 [DisT1_2 DisT2_2]].
        apply EnvironmentDis_Comb_comm in H0.
        generalize (EnvironmentDis_assoc _ _ _ _ _ H0 Dis').
        intros [envT1 [DisT1_1 DisT2_1]].
        eapply SEND with (env1 := envT1) (env2 := envT2).
        * apply EnvironmentDis_Comb_comm in DisT2_1.
          generalize (subst_lemma_TValue _ _ _ envT1 _ _ _ _ _ _ WT1_1 WT2 H DisT2_1).
          now simpl_subst_goal.
        * reflexivity.
        * admit. (* This holds *)
        * apply EnvironmentDis_Comb_comm in DisT2_2.
          generalize (subst_lemma_TValue _ _ _ envT2 _ _ _ _ _ _ WT1_2 WT2 H DisT2_2).
          now simpl_subst_goal.
    - rewrite subst_TGuard.
      generalize (EnvironmentDisCombination_insert _ _ _ _ _ e0).
      intros [env1' [env2' [L1 [L2 [Dis' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT [Eq1 Eq2]]]]]]]]];
      subst.
      (* x in left environment *)
      + apply EnvironmentDis_Comb_comm in H0.
        generalize (EnvironmentDis_assoc env4 env1' env2' env3 env0 H0 Dis').
        intros [envT [DisT1 DisT2]].
        apply EnvironmentDis_Comb_comm in DisT2.
        eapply GUARD with (env1 := envT) (env2 := env2').
        * assumption.
        * generalize (subst_lemma_TValue _ _ _ envT _ _ _ _ _ _ WT1 WT2 H DisT2).
          simpl_subst_goal; simpl; eauto.
        * now eapply subst_Guards_insert_None with (v := v0) in w.
        * assumption.
        * assumption.
      (* x in right environment *)
      + subst.
        generalize (EnvironmentDis_assoc_rev _ _ _ _ _ H0 Dis').
        intros [envT [DisT1 DisT2]].
        apply EnvironmentDis_Comb_comm in DisT2.
        eapply GUARD with (env1 := env1') (env2 := envT) (f := f).
        * assumption.
        * eapply subst_insert_None with (v := v0) in WT1.
          generalize WT1; now simpl_subst_goal.
        * eapply IHWT0; eauto.
        * assumption.
        * assumption.
      (* x in the both terms and is a base type *)
      + subst.
        generalize (EnvironmentDisCombination_insert_Type_eq _ _ _ _ _ _ e0);
        intros; subst.
        generalize (EnvironmentDis_assoc_rev _ _ _ _ _ H0 Dis').
        intros [envT2 [DisT1_2 DisT2_2]].
        apply EnvironmentDis_Comb_comm in H0.
        generalize (EnvironmentDis_assoc _ _ _ _ _ H0 Dis').
        intros [envT1 [DisT1_1 DisT2_1]].
        eapply GUARD with (env1 := envT1) (env2 := envT2) (f := f).
        * admit.
        * apply EnvironmentDis_Comb_comm in DisT2_1.
          generalize (subst_lemma_TValue _ _ _ envT1 _ _ _ _ _ _ WT1 WT2 H DisT2_1).
          now simpl_subst_goal.
        * apply EnvironmentDis_Comb_comm in DisT2_2.
          eapply IHWT0; eauto.
        * assumption.
        * assumption.
    - apply EnvironmentSubtype_insert_inv in e;
      destruct e as [env2' [T' [Sub' [EnvSub' [[Eq Un] | Eq]]]]];
      subst.
      + apply subst_insert_None with (v := v) in WT1.
        eapply WellTypedTerm_TValue_Un in WT2.
        * destruct WT2 as [env'' [Empty'' EnvSub'']].
          generalize (EnvDis_Sub env0 env3 env2' env'' env EnvSub' EnvSub'' H0).
          intros [envE [SubE DisE]].
          generalize (EnvDis_EmptyEnv_right _ _ _ Empty'' DisE); intros ->.
          eapply SUB; eassumption.
        * eapply Subtype_trans with (t2 := A); eassumption.
        * eassumption.
      + generalize (EnvDis_Sub env0 env3 env2' env3 env EnvSub' (EnvironmentSubtype_refl env3) H0).
        intros [env'' [EnvSub'' Dis'']].
        eapply SUB.
        eassumption.
        eassumption.
        eapply IHWT1; eauto using Subtype_trans with environment.
    - simpl; apply SINGLE; eapply IHWT1; eauto.
    - simpl; eapply SEQ.
      + eapply IHWT1; eauto.
      + eapply IHWT0; eauto.
    - constructor.
    - generalize (IHWT1 v x A A' env0 _ _ eq_refl H0 H1 H2).
      intros G.
      simpl_subst_goal; simpl.
      eapply FREE.
      generalize G. now simpl_subst_goal.
    - rewrite subst_GReceive.
      eapply RECEIVE.
      + reflexivity.
      + destruct o.
        * now left.
        * admit. (* Need lemma about base env*)
      + repeat rewrite raw_insert_zero in *.
        (*assert (Some ⌈ signature p m ⌉ :: Some (? e ^^ •) :: insert x A env1' = insert (2 + x) A (Some ⌈ signature p m ⌉ :: Some (? e ^^ •) :: env1')). admit.*)
        (*apply WellTypedTerm_TValue_raw_insert_None with (x := 2) in H0.*)
        (*assert (Some ⌈ signature p m ⌉ :: Some (? e ^^ •) :: env1' +ₑ raw_insert 2 None env2 ~= Some ⌈ signature p m ⌉ :: Some (? e ^^ •) :: env0). admit.*)
        (*generalize (IHWT1 (shift 2 v) _ _ A' (Some ⌈ signature p m ⌉ :: Some (? e ^^ •) :: env0) _ (raw_insert 2 None env2) H H0 H1 H3).*)
        (*simpl_subst_goal; simpl; simpl_lift_goal; simpl.*)
        (*assert (shift (l0 + 2) x1 = (lift 2 (l0 + 0) x1)).*)
  Admitted.


  (*Lemma WellTypedTerm_insert_None : forall p env t T x,*)
  (*  WellTypedTerm p env t T ->*)
  (*  WellTypedTerm p (raw_insert x None env) (shift x t) T.*)
  (*Proof.*)

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
    induction WT; intro; try discriminate; try apply EnvironmentSubtype_refl;
    try (now apply SubEnv_EmptyEnv_create_EmptyEnv).
    subst.
    eapply EnvSubtypeTrans.
    eassumption.
    generalize (IHWT eq_refl); intros Sub'.
    apply EnvironmentSubtype_length in H.
    apply create_EmptyEnv_length in H.
    now rewrite H.
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

  Lemma EnvironmentSubtype_middle' : forall env1_1 env1_2 env2 T,
    env1_1 ++ Some T :: env1_2 ≤ₑ env2 ->
    exists env2_1 env2_2 T',
    env1_1 ≤ₑ env2_1 /\ env1_2 ≤ₑ env2_2 /\ T ≤ T' /\
    ((env2 = env2_1 ++ None :: env2_2 /\ Unrestricted T') \/
    (env2 = env2_1 ++ Some T' :: env2_2)).
  Proof.
    induction env1_1; simpl; intros * Sub.
    - simpl_SubEnv; exists [], env0, T0; repeat split; eauto using EnvSubtypeRefl.
    - destruct a; simpl_SubEnv; subst.
      + apply IHenv1_1 in EnvSub;
        destruct EnvSub as [env2_1 [env2_2 [T' [Sub1 [Sub2 [Sub' [[Eq' Unr'] | Eq']]]]]]];
        subst;
        exists (None :: env2_1), env2_2, T'; repeat split; eauto;
        apply EnvSubtypeTrans with (env2 := Some T0 :: env1_1); constructor;
        eauto using EnvSubtypeRefl.
      + apply IHenv1_1 in EnvSub;
        destruct EnvSub as [env2_1 [env2_2 [T' [Sub1 [Sub2 [Sub' [[Eq' Unr'] | Eq']]]]]]];
        subst;
        exists (Some T0 :: env2_1), env2_2, T'; repeat split; eauto;
        apply EnvSubtypeTrans with (env2 := Some T0 :: env1_1); constructor;
        eauto using EnvSubtypeRefl, Subtype_refl.
      + apply IHenv1_1 in Sub0;
        destruct Sub0 as [env2_1 [env2_2 [T' [Sub1 [Sub2 [Sub' [[Eq' Unr'] | Eq']]]]]]];
        subst; exists (None :: env2_1), env2_2, T'; repeat split; eauto; now constructor.
  Qed.


  Lemma EnvironmentSubtype_middle'' : forall env1_1 env1_2 env2 A,
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

  (*Lemma WellTypedTerm_Var_inv : forall p env v T,*)
  (*  WellTypedTerm p env (TValue (ValueVar v)) T ->*)
  (*  exists env' T',*)
  (*  SingletonEnv env' /\ env ≤ₑ env' /\ T' ≤ T /\ lookup v env' = Some T'.*)
  (*Proof.*)
  (*  intros * WT.*)
  (*  remember (TValue (ValueVar v)) as V.*)
  (*  revert v HeqV.*)
  (*  induction WT; intros; subst; try discriminate.*)
  (*  - inversion HeqV; subst.*)
  (*    exists env, T; repeat split; eauto using EnvSubtypeRefl, Subtype_refl.*)
  (*  - generalize (IHWT v eq_refl).*)
  (*    intros [env' [T' [Singleton [EnvSub [Sub Lookup]]]]].*)
  (*    exists env', T'; repeat split;*)
  (*    try (eapply EnvSubtypeTrans || eapply Subtype_trans); eassumption.*)
  (*Qed.*)

  (*Lemma subst_lemma_TValue : forall p env1_1 env1_2 A B v1,*)
  (*  WellTypedTerm p (env1_1 ++ Some A :: env1_2) (TValue v1) B ->*)
  (*  forall v2 env2 A' env,*)
  (*  WellTypedTerm p env2 (TValue v2) A' ->*)
  (*  A' ≤ A ->*)
  (*  (env1_1 ++ env1_2) +ₑ env2 ~= env ->*)
  (*  WellTypedTerm p env (subst v2 (length env1_1) (TValue v1)) B.*)
  (*Proof.*)
  (*  intros * WT1 * WT2 Sub Dis.*)
  (*  destruct v1, v2; simpl_subst_goal; simpl; simpl_lift_goal; simpl.*)
  (*  - generalize (canonical_form_BTBool _ _ _ _ WT1); intros ->.*)
  (*    assert (Henv : env ≤ₑ create_EmptyEnv env). admit.*)
  (*    eapply SUB; eauto using Subtype_refl;*)
  (*    destruct b; constructor; apply create_EmptyEnv_EmptyEnv.*)
  (*  - generalize (canonical_form_BTBool _ _ _ _ WT1); intros ->.*)
  (*    assert (Henv : env ≤ₑ create_EmptyEnv env). admit.*)
  (*    eapply SUB; eauto using Subtype_refl;*)
  (*    destruct b; constructor; apply create_EmptyEnv_EmptyEnv.*)
  (*  - generalize (canonical_form_BTBool _ _ _ _ WT1); intros ->.*)
  (*    assert (Henv : env ≤ₑ create_EmptyEnv env). admit.*)
  (*    eapply SUB; eauto using Subtype_refl;*)
  (*    destruct b; constructor; apply create_EmptyEnv_EmptyEnv.*)
  (*  - generalize (canonical_form_BTUnit _ _ _ WT1); intros ->.*)
  (*    assert (Henv : env ≤ₑ create_EmptyEnv env). admit.*)
  (*    eapply SUB; eauto using Subtype_refl;*)
  (*    destruct b; constructor; apply create_EmptyEnv_EmptyEnv.*)
  (*  - generalize (canonical_form_BTUnit _ _ _ WT1); intros ->.*)
  (*    assert (Henv : env ≤ₑ create_EmptyEnv env). admit.*)
  (*    eapply SUB; eauto using Subtype_refl;*)
  (*    constructor; apply create_EmptyEnv_EmptyEnv.*)
  (*  - generalize (canonical_form_BTUnit _ _ _ WT1); intros ->.*)
  (*    assert (Henv : env ≤ₑ create_EmptyEnv env). admit.*)
  (*    eapply SUB; eauto using Subtype_refl;*)
  (*    constructor; apply create_EmptyEnv_EmptyEnv.*)
  (*  - unfold subst_idx. dblib_by_cases.*)
  (*    + apply WellTypedTerm_Var_inv in WT1;*)
  (*      destruct WT1 as [env' [T' [Singleton' [EnvSub' [Sub' Lookup']]]]].*)
  (*      (* Some A will be removed since v <> length env1_1 *)*)
  (*      (* env1_2 sub empty since v < length env1_1 *)*)
  (*      (* env2 sub empty since boolean *)*)
  (*      (* => env sub some singleton *)*)
  (*      assert (Henv : exists env'', env ≤ₑ env'' /\ SingletonEnv env''). admit.*)
  (*      destruct Henv as [env'' [EnvSub'' Singleton'']].*)
  (*      eapply SUB.*)
  (*      eassumption.*)
  (*      eassumption.*)
  (*      constructor.*)
  (*      assumption.*)
  (*      admit. (* This should hold, since lookup v env' = Some T' holds *)*)
  (*    + generalize (canonical_form_BTBool _ _ _ _ WT2); intros ->.*)
  (*      inversion Sub; subst.*)
  (*      (* B is BTBool: make canonical form lemma for variables *)*)
  (*      assert (H : B = TUBase BTBool). admit. subst.*)
  (*      (* env2 sub empty, since boolean *)*)
  (*      (* env sub empty, since env1_1 ++ Some A :: env1_2 is singleton,*)
  (*         i.e. env1_1 ++ Some A :: env1_2 is empty *)*)
  (*      assert (Henv : env ≤ₑ create_EmptyEnv env). admit.*)
  (*      eapply SUB; eauto using Subtype_refl;*)
  (*      destruct b; constructor; apply create_EmptyEnv_EmptyEnv.*)
  (*    + generalize (canonical_form_BTBool _ _ _ _ WT2); intros ->.*)
  (*      inversion Sub; subst.*)

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

