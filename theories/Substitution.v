(** * Substitution *)

From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.
From MailboxTypes Require Import TypingRules.
From MailboxTypes Require Export Dblib.DeBruijn.
From MailboxTypes Require Import Dblib.DblibTactics.
From MailboxTypes Require Import Dblib.Environments.

From Stdlib Require Import Lia.

Generalizable All Variables.

(** ** Definitions *)
Section subs_def.

  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

  Global Instance Var_Value : Var Value :=
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

  Global Instance Traverse_Value_Value : Traverse Value Value :=
  {
    traverse := traverse_Value
  }.

  Global Instance Traverse_Value_Term : Traverse Value Term :=
  {
    traverse := traverse_Term
  }.

  Global Instance Traverse_Value_Guard : Traverse Value Guard :=
  {
    traverse := traverse_Guard
  }.

  Global Instance TraverseVarInjective_Value : @TraverseVarInjective Value _ Value _.
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

  Global Instance TraverseVarInjective_Term : @TraverseVarInjective Value _ Term _.
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

  Global Instance TraverseFunctorial_Value : @TraverseFunctorial Value _ Value _.
  Proof. constructor; apply traverse_Value_functorial. Qed.

  Global Instance TraverseFunctorial_Term : @TraverseFunctorial Value _ Term _.
  Proof. constructor; apply traverse_Term_functorial. Qed.

  Global Instance TraverseIdentifiesVar_Value : TraverseIdentifiesVar.
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

  Global Instance TraverseRelative_Value : @TraverseRelative Value Value _.
  Proof. constructor; apply traverse_Value_relative. Qed.

  Global Instance TraverseRelative_Term : @TraverseRelative Value Term _.
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

  Global Instance TraverseVarIsIdentity_Value : @TraverseVarIsIdentity Value _ Value _.
  Proof. constructor; apply traverse_Value_identity. Qed.

  Global Instance TraverseVarIsIdentity_Term : @TraverseVarIsIdentity Value _ Term _.
  Proof. constructor; apply traverse_Term_identity. Qed.

  (* First argument: Value *)
  (* Second argument: Variable *)
  (* Third argument: Term *)
  (*Type @subst Value Term.*)


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

  Lemma shift_TLet : forall t1 t2 x,
    shift x (TLet t1 t2) = TLet (shift x t1) (shift (1 + x) t2).
  Proof.
    intros.
    simpl_lift_goal; simpl.
    f_equal.
    assert ((forall l x0 : nat, ValueVar (shift (l + 1 + x) x0) = ValueVar (shift (l + S x) x0))).
    {
      intros; f_equal. now replace (l + 1 + x) with (l + S x) by lia.
    }
    generalize (traverse_relative (fun l x0 : nat => ValueVar (shift (l + x) x0)) (fun l x0 : nat => ValueVar (shift (l + S x) x0)) 1 t2).
    intros; generalize (H 1 0); intros.
    now apply H0.
  Qed.

  Lemma WellTypedTerm_raw_insert_None : forall p env t x T,
    WellTypedTerm p env t T ->
    WellTypedTerm p (raw_insert x None env) (shift x t) T.
  Proof.
    intros * WT.
    revert x.
    induction WT using @WellTypedTerm_ind3 with
      (P0 := fun env gs T E (WG : WellTypedGuards p env gs T E) =>
        forall x,
        WellTypedGuards p (raw_insert x None env) (List.map (shift x) gs) T E
      )
      (P1 := fun env g T E (WG : WellTypedGuard p env g T E) =>
        forall x,
          WellTypedGuard p (raw_insert x None env) (shift x g) T E
      ); intros.
    - assert (WT' : WellTypedTerm p (insert x T env) (TValue (ValueVar x)) T) by now constructor.
      generalize (WellTypedTerm_TValue_raw_insert_None p (insert x T env) (ValueVar x) x0 T WT').
      now simpl_lift_goal.
    - admit.
    - admit.
    - admit.
    - generalize (IHWT x); simpl_lift_goal; simpl; econstructor; try eassumption.
    - rewrite shift_TLet.
     eapply LET with (env2 := raw_insert x None env2); try eassumption.
      + admit. (* Need new lemma *)
      + apply IHWT1.
      + rewrite insert_insert by lia.
        apply IHWT2.
    - simpl_lift_goal; simpl.
      apply SPAWN with (env := raw_insert x None env).
      + generalize (IHWT x); now simpl_lift_goal.
      + admit. (* Need lemma *)
    - simpl_lift_goal; simpl; constructor; now apply EmptyEnv_raw_insert_None.
    - simpl_lift_goal; simpl; econstructor.
      + generalize (IHWT1 x); simpl_lift_goal; simpl; intros WT'; apply WT'.
      + eassumption.
      + apply EnvDis_insert_None; eassumption.
      + generalize (IHWT2 x); simpl_lift_goal; simpl; intros WT'; apply WT'.
    (* TODO : Continue *)
  Admitted.

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
      + now apply WellTypedTerm_TValue_insert_None_gt in WT.
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
      rewrite EmptyEnv_raw_insert_None; eauto
    );
    try (
      simpl_subst_goal; simpl; simpl_lift_goal;
      constructor; eauto
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
    - simpl; generalize (IHWT x v env' eq_refl); eauto.
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
      intros [env1' [env2' [L1 [L2 [Comb2 [[Eq1 Eq2] | [[Eq1 Eq2] | [A1 [A2 [Eq1 [Eq2 TComb]]]]]]]]]]];
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
        destruct v.
        * repeat (simpl_lift_goal; simpl).
          generalize (canonical_form_BTBool _ _ _ _ WT2).
          intros ->.
          apply weak_BTBool_2 in WT2.
          inversion H; subst.
          inversion TComb; subst.
          generalize (EnvironmentDisjointCombination_Subtype_Empty _ _ _ _ H0 (create_EmptyEnv_EmptyEnv env4) WT2).
          intros Sub'.
          eapply SUB; try apply Subtype_refl; try eassumption.
          eapply LET.
          -- eassumption.
          -- eapply IHWT1_1 with (A' := TUBase BTBool) (env2 := create_EmptyEnv env1').
             ++ reflexivity.
             ++ destruct b; eauto with environment.
             ++ apply Subtype_refl.
             ++ apply EnvironmentDisjointCombination_Empty; eauto with environment.
          -- eapply IHWT1_2 with (A' := TUBase BTBool) (env2 := (None :: create_EmptyEnv env2')) (env1 := Some ⌊ T1 ⌋ :: env2').
             ++ rewrite raw_insert_zero.
                rewrite raw_insert_successor.
                rewrite lookup_zero; simpl.
                reflexivity.
             ++ destruct b; repeat constructor; apply create_EmptyEnv_EmptyEnv.
             ++ apply Subtype_refl.
             ++ rewrite raw_insert_zero.
                constructor.
                apply EnvironmentDisjointCombination_Empty; eauto with environment.
        * repeat (simpl_lift_goal; simpl).
          generalize (canonical_form_BTUnit _ _ _ WT2).
          intros ->.
          apply weak_BTUnit_2 in WT2.
          inversion H; subst.
          inversion TComb; subst.
          generalize (EnvironmentDisjointCombination_Subtype_Empty _ _ _ _ H0 (create_EmptyEnv_EmptyEnv env4) WT2).
          intros Sub'.
          eapply SUB; try apply Subtype_refl; try eassumption.
          eapply LET.
          -- eassumption.
          -- eapply IHWT1_1 with (A' := TUBase BTUnit) (env2 := create_EmptyEnv env1').
             ++ reflexivity.
             ++ eauto with environment.
             ++ apply Subtype_refl.
             ++ apply EnvironmentDisjointCombination_Empty; eauto with environment.
          -- eapply IHWT1_2 with (A' := TUBase BTUnit) (env2 := (None :: create_EmptyEnv env2')) (env1 := Some ⌊ T1 ⌋ :: env2').
             ++ rewrite raw_insert_zero.
                rewrite raw_insert_successor.
                rewrite lookup_zero; simpl.
                reflexivity.
             ++ repeat constructor; apply create_EmptyEnv_EmptyEnv.
             ++ apply Subtype_refl.
             ++ rewrite raw_insert_zero.
                constructor.
                apply EnvironmentDisjointCombination_Empty; eauto with environment.
        * repeat (simpl_lift_goal; simpl).
          apply weak_ValueVar_3 in WT2.
          destruct WT2 as [env4' [T' [Eq' [Sub [SubEnv WT2]]]]].
          subst.
          generalize (EnvironmentDisjointCombination_insert_left _ _ _ _ _ H0).
          intros [env3' [env0' [[-> ->] | [c [-> [-> ->]]]]]].
          -- generalize (EnvironmentDisjointCombination_Subtype_Empty_insert _ _ _ (create_EmptyEnv env4') _ _ H0 (create_EmptyEnv_EmptyEnv env4') SubEnv).
             intros Sub'.
             eapply SUB with (env2 := insert v A env3').
             ++ eapply EnvironmentSubtype_trans.
                eassumption.
                apply EnvironmentSubtype_insert_Subtype.
                eapply Subtype_trans; eassumption.
             ++ eapply Subtype_refl.
             ++ generalize (EnvironmentCombination_raw_insert_None _ _ _ _ Comb2).
                intros [env1'' [env2'' [Eq1 [? [Eq2 [? Comb']]]]]].
                eapply LET with (env1 := insert v A1 env1'') (env2 := (insert v A2 env2'')).
                ** now apply EnvironmentCombination_insert_both.
                ** eapply IHWT1_1 with (A := A1) (A' := A1) (env2 := insert v A1 (create_EmptyEnv env1'')).
                   --- reflexivity.
                   --- eauto with environment.
                   --- apply Subtype_refl.
                   --- rewrite Eq1.
                       apply EnvironmentDisjointCombination_insert_EmptyEnv;
                       eauto with environment.
                ** eapply IHWT1_2 with (A := A2) (A' := A2) (env2 := insert (S v) A2 (None :: create_EmptyEnv env2'')) (env1 := Some ⌊ T1 ⌋ :: env2').
                   --- rewrite raw_insert_successor.
                       rewrite raw_insert_zero.
                       now rewrite lookup_zero.
                   --- repeat constructor; apply create_EmptyEnv_EmptyEnv.
                   --- apply Subtype_refl.
                   --- rewrite raw_insert_zero.
                       rewrite raw_insert_successor.
                       rewrite lookup_zero.
                       simpl.
                       constructor.
                       rewrite Eq2.
                       apply EnvironmentDisjointCombination_insert_EmptyEnv;
                       eauto with environment.
          -- generalize (EnvironmentDisjointCombination_Subtype_Empty_insert_Base _ _ _ (create_EmptyEnv env4') _ _ H0 (create_EmptyEnv_EmptyEnv env4') SubEnv).
             intros Sub'.
             eapply SUB with (env2 := insert v A env3').
             ++ eapply EnvironmentSubtype_trans.
                eassumption.
                apply EnvironmentSubtype_insert_Subtype.
                eapply Subtype_trans; eassumption.
             ++ eapply Subtype_refl.
             ++ inversion Sub; subst.
                inversion H; subst.
                inversion TComb; subst.
                generalize (EnvironmentCombination_raw_insert_Base _ _ _ _ _ Comb2).
                intros [env1'' [env2'' [Comb' [[-> ->] | [[-> ->] | [-> ->]]]]]].
                ** eapply LET with (env1 := insert v (TUBase c) env1'') (env2 := (insert v (TUBase c) env2'')).
                   --- apply EnvironmentCombination_insert_both; auto.
                   --- eapply IHWT1_1 with (A := TUBase c) (A' := TUBase c) (env2 := insert v (TUBase c) (create_EmptyEnv env1'')).
                       +++ reflexivity.
                       +++ eauto with environment.
                       +++ apply Subtype_refl.
                       +++ apply EnvironmentDisjointCombination_insert_Base;
                           eauto with environment.
                   --- eapply IHWT1_2 with (A := TUBase c) (A' := TUBase c) (env2 := insert (S v) (TUBase c) (None :: create_EmptyEnv env2'')) (env1 := Some ⌊ T1 ⌋ :: (raw_insert v None env2'')).
                       +++ reflexivity.
                       +++ repeat constructor; apply create_EmptyEnv_EmptyEnv.
                       +++ apply Subtype_refl.
                       +++ rewrite raw_insert_zero.
                           rewrite raw_insert_successor.
                           rewrite lookup_zero.
                           simpl.
                           constructor.
                           apply EnvironmentDisjointCombination_insert_EmptyEnv;
                           eauto with environment.
                ** eapply LET with (env1 := insert v (TUBase c) env1'') (env2 := (insert v (TUBase c) env2'')).
                   --- apply EnvironmentCombination_insert_both; auto.
                   --- eapply IHWT1_1 with (A := TUBase c) (A' := TUBase c) (env2 := insert v (TUBase c) (create_EmptyEnv env1'')).
                       +++ reflexivity.
                       +++ eauto with environment.
                       +++ apply Subtype_refl.
                       +++ apply EnvironmentDisjointCombination_insert_EmptyEnv;
                           eauto with environment.
                   --- eapply IHWT1_2 with (A := TUBase c) (A' := TUBase c) (env2 := insert (S v) (TUBase c) (None :: create_EmptyEnv env2'')) (env1 := Some ⌊ T1 ⌋ :: (insert v (TUBase c) env2'')).
                       +++ rewrite raw_insert_zero.
                           rewrite raw_insert_successor.
                           now rewrite lookup_zero.
                       +++ repeat constructor; apply create_EmptyEnv_EmptyEnv.
                       +++ apply Subtype_refl.
                       +++ rewrite raw_insert_zero.
                           rewrite raw_insert_successor.
                           rewrite lookup_zero.
                           simpl.
                           constructor.
                           apply EnvironmentDisjointCombination_insert_Base;
                           eauto with environment.
                ** eapply LET with (env1 := insert v (TUBase c) env1'') (env2 := (insert v (TUBase c) env2'')).
                   --- apply EnvironmentCombination_insert_both; auto.
                   --- eapply IHWT1_1 with (A := TUBase c) (A' := TUBase c) (env2 := insert v (TUBase c) (create_EmptyEnv env1'')).
                       +++ reflexivity.
                       +++ eauto with environment.
                       +++ apply Subtype_refl.
                       +++ apply EnvironmentDisjointCombination_insert_Base;
                           eauto with environment.
                   --- eapply IHWT1_2 with (A := TUBase c) (A' := TUBase c) (env2 := insert (S v) (TUBase c) (None :: create_EmptyEnv env2'')) (env1 := Some ⌊ T1 ⌋ :: (insert v (TUBase c) env2'')).
                       +++ rewrite raw_insert_zero.
                           rewrite raw_insert_successor.
                           now rewrite lookup_zero.
                       +++ repeat constructor; apply create_EmptyEnv_EmptyEnv.
                       +++ apply Subtype_refl.
                       +++ rewrite raw_insert_zero.
                           rewrite raw_insert_successor.
                           rewrite lookup_zero.
                           simpl.
                           constructor.
                           apply EnvironmentDisjointCombination_insert_Base;
                           eauto with environment.
    - rewrite subst_TSpawn. admit.
      (*generalize (secondEnvironment_insert x A env env1 HeqE1).*)
      (*intros [Eq1 Eq2].*)
      (*rewrite Eq1 in *.*)
      (*apply secondEnvironment_insert_inv in HeqE1.*)
      (*destruct HeqE1 as [env2' [T' [Eq3 [Sub' Eq4]]]].*)
      (*assert (exists env0', env2' +ₑ env2 ~= env0') by admit.*)
      (*destruct H1 as [env0' Comb'].*)
      (*eapply SPAWN; auto.*)
      (*+ eapply IHWT1.*)
      (*  * eassumption.*)
      (*  * eassumption.*)
      (*  * eapply Subtype_trans; eassumption.*)
      (*  * rewrite <- Eq4 in H0.*)
      (*    apply Comb'.*)
      (*+ admit.*)
      (**)
      (*eapply SPAWN; auto.*)
      (*assert (exists env' T, env = insert x T ⌈ env' ⌉ₑ) by admit.*)
      (*destruct H1 as [env' [T Eq]].*)
      (*assert (A ≤ T) by admit.*)
      (*econstructor.*)
      (*+ eapply IHWT1.*)
      (*  * eassumption.*)
      (*  * eassumption.*)
      (*  * eapply Subtype_trans; eassumption.*)
      (*  * admit.*)
      (*+ admit.*)

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
        admit.
  Admitted.

  End subs_def.
