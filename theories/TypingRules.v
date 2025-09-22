(** * Typing rules of the Pat programming language *)

From MailboxTypes Require Export Types.
From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Message.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.

From Stdlib Require Import Lists.List.
Import ListNotations.

(** ** Definition of typing rules *)
Section typing_rules_def.

  Generalizable All Variables.
  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

  Inductive WellTypedTerm (prog : Prog) : Env -> Term -> TUsage -> Prop :=
    (* Var *)
  | VAR   : forall env x T,
      EmptyEnv env ->
      WellTypedTerm prog (insert x T env) (TValue (ValueVar x)) T
    (* Consts *)
    | TRUE  : forall env,
        EmptyEnv env ->
        WellTypedTerm prog env (TValue (ValueBool true)) (TUBase BTBool)
    | FALSE : forall env,
        EmptyEnv env ->
        WellTypedTerm prog env (TValue (ValueBool false)) (TUBase BTBool)
    | UNIT  : forall env,
        EmptyEnv env ->
        WellTypedTerm prog env (TValue ValueUnit) (TUBase BTUnit)
    (* App *)
    | APP : forall env v definition bodyType argumentType term,
        definitions prog definition = (FunDef definition argumentType bodyType term) ->
        WellTypedTerm prog env (TValue v) argumentType ->
        WellTypedTerm prog env (TApp definition v) bodyType
    (* Let *)
    | LET   : forall env env1 env2 T1 T2 t1 t2,
        env1 ▷ₑ env2 ~= env ->
        WellTypedTerm prog env1 t1 ⌊ T1 ⌋ ->
        WellTypedTerm prog (insert 0 ⌊ T1 ⌋ env2) t2 T2 ->
        WellTypedTerm prog env (TLet t1 t2) T2
    (* Spawn *)
    | SPAWN : forall env env' t,
        WellTypedTerm prog env t (TUBase BTUnit) ->
        env' = ⌈ env ⌉ₑ ->
        WellTypedTerm prog env' (TSpawn t) (TUBase BTUnit)
    (* New *)
    | NEW : forall env, EmptyEnv env -> WellTypedTerm prog env TNew (? 𝟙 ^^ •)
    (* Send *)
    | SEND : forall env env1 env2 T m v1 v2,
        WellTypedTerm prog env1 (TValue v1) (! « m » ^^ ◦) ->
        signature prog m = T ->
        env1 +ₑ env2 ~= env ->
        WellTypedTerm prog env2 (TValue v2) ⌈ T ⌉ ->
        WellTypedTerm prog env (TSend v1 m v2) (TUBase BTUnit)
    (* Guard *)
    | GUARD : forall env env1 env2 guards v T e f,
        env1 +ₑ env2 ~= env ->
        WellTypedTerm prog env1 (TValue v) (? f ^^ •) ->
        WellTypedGuards prog env2 guards T f ->
        e ⊑ f ->
        f ⊧ f ->
        WellTypedTerm prog env (TGuard v e guards) T
    (* Sub *)
    | SUB : forall t env1 env2 T1 T2,
        env1 ≤ₑ env2 ->
        T1 ≤ T2 ->
        WellTypedTerm prog env2 t T1 ->
        WellTypedTerm prog env1 t T2
  with WellTypedGuards (prog : Prog) : Env -> list Guard -> TUsage -> MPattern -> Prop :=
    | SINGLE : forall T e env g,
        WellTypedGuard prog env g T e ->
        WellTypedGuards prog env (g :: nil) T e
    | SEQ : forall T e es env guards g,
        WellTypedGuard prog env g T e ->
        WellTypedGuards prog env guards T es ->
        WellTypedGuards prog env (g :: guards) T (e ⊕ es)
  with WellTypedGuard (prog : Prog) : Env -> Guard -> TUsage -> MPattern -> Prop :=
    (* Fail *)
    | FAIL : forall t env, WellTypedGuard prog env GFail t 𝟘
    (* Free *)
    | FREE : forall t env T,
        WellTypedTerm prog env t T ->
        WellTypedGuard prog env (GFree t) T 𝟙
    (* Receive *)
    | RECEIVE : forall t m env BT T e,
        signature prog m = BT ->
        BaseType BT \/ BaseEnv env ->
        WellTypedTerm prog (insert 0 ⌈ BT ⌉ (insert 0 (? e ^^ •) env)) t T ->
        WellTypedGuard prog env (GReceive m t) T (« m » ⊙ e).

  Inductive WellTypedDefinition (prog : Prog) : FunctionDefinition -> Prop :=
    | FUNDEF : forall defName argumentType body bodyType,
        WellTypedTerm prog [Some argumentType] body bodyType ->
        WellTypedDefinition prog (FunDef defName argumentType bodyType body).

  Inductive WellTypedProgram (prog : Prog) : Prop :=
    PROG :
      (forall def, WellTypedDefinition prog (definitions prog def)) ->
      WellTypedTerm prog [] (initialTerm prog) (TUBase BTUnit) ->
      WellTypedProgram prog.

    Scheme WellTypedTerm_ind3 := Induction for WellTypedTerm Sort Prop
      with WellTypedGuards_ind3 := Induction for WellTypedGuards Sort Prop
      with WellTypedGuard_ind3 := Induction for WellTypedGuard Sort Prop.


  (** Definition D.3 of cruftless.
    An environment is cruftless for a term, if the term is well-typed under
    the environment and the domain of the environment is equal to the
    free variables in the term.
  *)
  Definition Cruftless {p : Prog} (env : Env) (m : Term) :=
    exists T, WellTypedTerm p env m T /\ EnvEqFV env m.

End typing_rules_def.

Hint Constructors WellTypedTerm : environment.

(** ** Properties of well-typed terms *)
Section well_typed_properties.

  Generalizable All Variables.
  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

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

  Lemma weak_BTBool_1 : forall p env b T,
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

  Lemma weak_BTBool_2 : forall p env b T,
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

  Lemma weak_BTUnit_2 : forall p env T,
    WellTypedTerm p env (TValue ValueUnit) T ->
    env ≤ₑ create_EmptyEnv env.
  Proof.
    intros * WT.
    remember (TValue ValueUnit) as V.
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

  Lemma weak_ValueVar_2 : forall p env x T,
    WellTypedTerm p env (TValue (ValueVar x)) T ->
    exists env' T',
      T' ≤ T /\
      EmptyEnv env' /\
      env ≤ₑ insert x T' env' /\
      WellTypedTerm p (insert x T' env') (TValue (ValueVar x)) T'.
  Proof.
    intros * WT.
    remember (TValue (ValueVar x)) as V.
    revert HeqV.
    induction WT; intros; try discriminate.
    - inversion HeqV; subst.
      exists env, T; repeat split; eauto with environment.
      apply Subtype_refl.
    - subst.
      generalize (IHWT eq_refl);
      intros [env' [T' [Sub' [Empty' [SubEnv' WT']]]]].
      exists env', T'; repeat split; eauto with environment.
      + eapply Subtype_trans; eassumption.
      + eapply EnvironmentSubtype_trans; eassumption.
  Qed.

  Lemma TLet_inv : forall prog env t1 t2 T,
    WellTypedTerm prog env (TLet t1 t2) T ->
    exists env' T' T1 env1 env2,
      env1 ▷ₑ env2 ~= env' /\
      WellTypedTerm prog env1 t1 ⌊ T1 ⌋ /\
      WellTypedTerm prog (insert 0 ⌊ T1 ⌋ env2) t2 T' /\
      env ≤ₑ env' /\
      T' ≤ T.
  Proof.
    intros * WT.
    remember (TLet t1 t2) as TT.
    revert t1 t2 HeqTT.
    induction WT; intros; inversion HeqTT; subst.
    - exists env, T2, T1, env1, env2; repeat split;
      eauto using Subtype_refl with environment.
    - generalize (IHWT _ _ eq_refl).
      intros [env' [T' [T1' [env1' [env2' [? [? [? [? ?]]]]]]]]].
      exists env', T', T1', env1', env2'; repeat split;
      eauto using Subtype_trans, EnvironmentSubtype_trans with environment.
  Qed.

  Lemma weak_ValueVar_3 : forall p env x T,
    WellTypedTerm p env (TValue (ValueVar x)) T ->
    exists env' T',
      env = insert x T' env' /\
      T' ≤ T /\
      env' ≤ₑ create_EmptyEnv env' /\
      WellTypedTerm p (insert x T' env') (TValue (ValueVar x)) T.
  Proof.
    intros * WT.
    remember (TValue (ValueVar x)) as V.
    revert HeqV.
    induction WT; intros; try discriminate.
    - inversion HeqV; subst.
      exists env, T; repeat split; eauto with environment.
      apply Subtype_refl.
    - subst.
      generalize (IHWT eq_refl).
      intros [env' [T' [Eq [Sub [EnvSub WT']]]]].
      subst.
      generalize (EnvironmentSubtype_insert_right_inv _ _ _ _ H).
      intros [env1' [T1' [Sub' Eq']]].
      subst.
      exists env1', T1'; repeat split; eauto with environment.
      + eapply Subtype_trans with (t2 := T').
        assumption.
        eapply Subtype_trans with (t2 := T1); assumption.
      + now apply EnvironmentSubtype_insert_Empty in H.
  Qed.

  Lemma WellTypedTerm_TValue_inv : forall p env v T,
    WellTypedTerm p env (TValue v) T ->
    (* v is a variable *)
    (exists x env' T',
      T' ≤ T /\
      EmptyEnv env' /\
      env ≤ₑ insert x T' env' /\
      v = ValueVar x /\
      WellTypedTerm p (insert x T' env') (TValue (ValueVar x)) T') \/
    (* v is a boolean *)
    (exists b env',
      T = TUBase BTBool /\
      EmptyEnv env' /\
      env ≤ₑ env' /\
      v = ValueBool b /\
      WellTypedTerm p env' (TValue (ValueBool b)) (TUBase BTBool)) \/
    (* v is unit *)
    (exists env',
      T = TUBase BTUnit /\
      EmptyEnv env' /\
      env ≤ₑ env' /\
      v = ValueUnit /\
      WellTypedTerm p env' (TValue ValueUnit) (TUBase BTUnit)).
  Proof.
    intros * WT.
    destruct v.
    - right; left.
      generalize (canonical_form_BTBool _ _ _ _ WT); intros ->.
      apply weak_BTBool_2 in WT.
      exists b, (create_EmptyEnv env); repeat split; eauto with environment.
      destruct b; constructor; eauto with environment.
    - repeat right.
      generalize (canonical_form_BTUnit _ _ _ WT); intros ->.
      apply weak_BTUnit_2 in WT.
      exists (create_EmptyEnv env); repeat split; eauto with environment.
    - left.
      apply weak_ValueVar_2 in WT.
      destruct WT as [env' [T' [Sub [Empty [Sub' WT]]]]].
      exists v, env', T'; repeat split; eauto.
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

  Lemma WellTypedTerm_insert_Sub : forall x prog env T1 T1' T2 t,
    T1' ≤ T1 ->
    WellTypedTerm prog (insert x T1 env) t T2 ->
    WellTypedTerm prog (insert x T1' env) t T2.
  Proof.
    intros * Sub WT.
    eapply SUB with (env2 := insert x T1 env).
    - now apply EnvironmentSubtype_insert_T.
    - apply Subtype_refl.
    - assumption.
  Qed.

  (* TODO: Need to define environment splits before proving these lemmas *)

  (*Lemma WellTypedEnvSub_TValue :*)
  (*  forall p env v T,*)
  (*  WellTypedTerm p env (TValue v) T ->*)
  (*  exists env1 env2 env3 T',*)
  (*    env1,, env2 ~= env /\*)
  (*    T' ≤ T /\*)
  (*    WellTypedTerm p env3 (TValue v) T' /\*)
  (*    @Cruftless p env1 (TValue v) /\*)
  (*    env1 ≼ₑ env3 /\*)
  (*    env2 ≤ₑ create_EmptyEnv env2.*)
  (*Proof.*)
  (*Admitted.*)

  (** Lemma D.4 *)
  (*Lemma WellTypedEnvSub :*)
  (*  forall T p env m,*)
  (*  WellTypedTerm p env m T ->*)
  (*  exists env1 env2 env3 T',*)
  (*    env1,, env2 ~= env /\*)
  (*    T' ≤ T /\*)
  (*    WellTypedTerm p env3 m T' /\*)
  (*    @Cruftless p env1 m /\*)
  (*    env1 ≼ₑ env3 /\*)
  (*    env2 ≤ₑ create_EmptyEnv env2.*)
  (*Proof.*)
  (*Admitted.*)

End well_typed_properties.
