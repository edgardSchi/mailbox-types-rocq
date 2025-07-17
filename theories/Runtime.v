(** * Operational Semantics of Pat *)

From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.
From MailboxTypes Require Import TypingRules.
From MailboxTypes Require Import Substitution.

From Stdlib Require Import ListSet.
From Stdlib Require Import PeanoNat.

Generalizable All Variables.

Section runtime_def.
  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

  (**
    A stack is a simply a list of terms. Due to the usage of deBruijn indices
    we don't include variable names in frames.
    We will always replace variable 0.
  *)
  Definition Stack := list Term.

  Inductive Configuration : Type :=
    | ConfConf : Term -> Stack -> Configuration
    | ConfMessage : VarName -> Message -> Value -> Configuration
    | ConfParallel : Configuration -> Configuration -> Configuration
    | ConfRestr : Configuration -> Configuration.

  Fixpoint lower_conf (i : VarName) (c : Configuration) : Configuration :=
    match c with
    | ConfConf t s => ConfConf (lower i t) s
    | ConfMessage x m v => ConfMessage (lower_Var i x) m (lower_Value i v)
    | ConfParallel c1 c2 => ConfParallel (lower_conf i c1) (lower_conf i c2)
    | ConfRestr c => ConfRestr (lower_conf (S i) c)
    end.

  Fixpoint exchange_conf (i : VarName) (c : Configuration) : Configuration :=
    match c with
    | ConfConf t s => ConfConf (exchange i t) s
    | ConfMessage x m v => ConfMessage (exchange_Var i x) m (exchange_Value i v)
| ConfParallel c1 c2 => ConfParallel (exchange_conf i c1) (exchange_conf i c2)
    | ConfRestr c => ConfRestr (exchange_conf (S i) c)
    end.

  Fixpoint FV_conf (c : Configuration) : set nat :=
    match c with
    | ConfConf t s => FV t
    | ConfMessage x m v =>
        set_union Nat.eq_dec [x] (FV_val v)
    | ConfParallel c1 c2 =>
        set_union Nat.eq_dec (FV_conf c1) (FV_conf c2)
    | ConfRestr c =>
        (downShift 1 (set_remove Nat.eq_dec 0 (FV_conf c)))
    end.

  Inductive StructCongr : Configuration -> Configuration -> Prop :=
    | CongrParSym : forall c d, StructCongr (ConfParallel c d) (ConfParallel d c)
    | CongrAssoc : forall c d e,
        StructCongr (ConfParallel c (ConfParallel d e)) (ConfParallel (ConfParallel c d) e)
    | CongrRestrComm : forall c,
        StructCongr (ConfRestr (ConfRestr c)) (ConfRestr (ConfRestr (exchange_conf 0 c)))
    | CongrRestrExt : forall c d,
        ~ In 0 (FV_conf d) ->
        StructCongr (ConfRestr (ConfParallel c d)) (ConfParallel (ConfRestr c) (lower_conf 0 d))
    | CongrRefl : forall c, StructCongr c c
    | CongrSym : forall c d, StructCongr c d -> StructCongr d c
    | CongrTrasn : forall c d e, StructCongr c d -> StructCongr d e -> StructCongr c e.

  Inductive Step (prog : Prog) : Configuration -> Configuration -> Prop :=
    | stepLet : forall t1 t2 stack,
        Step prog (ConfConf (TLet t1 t2) stack) (ConfConf t1 (t2 :: stack))
    | stepReturn : forall (v : Value) t stack,
        Step prog (ConfConf (TValue v) (t :: stack)) (ConfConf (subst v 0 t) stack)
    | stepApp : forall v stack definition bodyType argumentType t,
        definitions prog definition = (FunDef definition argumentType bodyType t) ->
        Step prog (ConfConf (TApp definition v) stack) (ConfConf (subst v 0 t) stack)
    | stepNew : forall stack,
        Step prog (ConfConf TNew stack) (ConfRestr (ConfConf (TValue (ValueVar 0)) stack))
    | stepSend : forall stack x m v,
        Step prog (ConfConf (TSend (ValueVar x) m v) stack)
                  (ConfParallel (ConfConf (TValue (ValueUnit)) stack) (ConfMessage x m v))
    | stepSpawn : forall stack t,
        Step prog (ConfConf (TSpawn t) stack)
                  (ConfParallel (ConfConf (TValue (ValueUnit)) stack) (ConfConf t []))
    | stepFree : forall stack e guards t,
        Exists (fun g => g = GFree t) guards ->
        Step prog (ConfRestr (ConfConf (TGuard (ValueVar 0) e guards) stack))
        (ConfConf t stack)
    | stepReceive : forall stack e guards x m v t,
        Exists (fun g => g = GReceive m t) guards ->
        Step prog (ConfParallel (ConfConf (TGuard (ValueVar x) e guards) stack) (ConfMessage x m v))
        (ConfConf ((subst v 0) (subst (ValueVar x) 0 t)) stack)
    | stepNu : forall c d,
        Step prog c d ->
        Step prog (ConfRestr c) (ConfRestr d)
    | stepPar : forall c c' d,
        Step prog c c' ->
        Step prog (ConfParallel c d) (ConfParallel c' d)
    | stepStruct : forall c c' d d',
        StructCongr c c' ->
        StructCongr d' d ->
        Step prog c' d' ->
        Step prog c d.

  Definition RuntimeEnv := env TType.

  Inductive RuntimeEnvironmentCombination : RuntimeEnv -> RuntimeEnv -> RuntimeEnv -> Prop :=
      RuntimeEnvCombEmpty : RuntimeEnvironmentCombination nil nil nil
    (* Special constructor for our representation of environments *)
    | RuntimeEnvCombNone : forall env1 env2 env,
        RuntimeEnvironmentCombination env1 env2 env ->
        RuntimeEnvironmentCombination (None :: env1) (None :: env2) (None :: env)
    | RuntimeEnvCombLeft : forall env1 env2 env T,
        RuntimeEnvironmentCombination env1 env2 env ->
        RuntimeEnvironmentCombination (Some T :: env1) (None :: env2) (Some T :: env)
    | EnvCombRight : forall env1 env2 env T,
        RuntimeEnvironmentCombination env1 env2 env ->
        RuntimeEnvironmentCombination (None :: env1) (Some T :: env2) (Some T :: env)
    | EnvCombBoth : forall T env1 env2 env T1 T2,
        RuntimeEnvironmentCombination env1 env2 env ->
        T1 ⊞ T2 ~= T ->
        RuntimeEnvironmentCombination (Some T1 :: env1) (Some T2 :: env2) (Some T :: env).

  Inductive RuntimeSubtype : TType -> TType -> Prop :=
      SubtypeBase : forall c, RuntimeSubtype (TTBase c) (TTBase c)
    | SubtypeInput : forall e f,
        MPInclusion e f -> RuntimeSubtype (TTMailbox (MTInput e)) (TTMailbox (MTInput f))
    | SubtypeOutput : forall e f,
        MPInclusion f e -> RuntimeSubtype (TTMailbox (MTOutput e)) (TTMailbox (MTOutput f)).

  Definition ReliableType (T : TType) : Prop :=
    ~ (RuntimeSubtype T (TTMailbox (? 𝟘))).

  Definition ReliableEnv : RuntimeEnv -> Prop :=
    ForallMaybe ReliableType.

  Inductive RuntimeEnvironmentSubtype : RuntimeEnv -> RuntimeEnv -> Prop :=
    | EnvSubtypeNone : forall env1 env2,
        RuntimeEnvironmentSubtype env1 env2 ->
        RuntimeEnvironmentSubtype (None :: env1) (None :: env2)
    | EnvSubtypeDrop : forall env1 env2 T,
        RuntimeEnvironmentSubtype env1 env2 ->
        RuntimeEnvironmentSubtype (Some T :: env1) (None :: env2)
    | EnvSubtypeSub : forall env1 env2 T1 T2,
        RuntimeSubtype T1 T2 ->
        RuntimeEnvironmentSubtype env1 env2 ->
        RuntimeEnvironmentSubtype (Some T1 :: env1) (Some T2 :: env2)
    | EnvSubtypeTrans : forall env1 env2 env3,
        RuntimeEnvironmentSubtype env1 env2 ->
        RuntimeEnvironmentSubtype env2 env3 ->
        RuntimeEnvironmentSubtype env1 env3
    | EnvSubtypeRefl : forall env, RuntimeEnvironmentSubtype env env.

  Inductive WellTypedConfig (prog : Prog) : RuntimeEnv -> Configuration -> Prop :=
    | NU : forall env c,
        WellTypedConfig prog (Some (TTMailbox (? 𝟙)) :: env) c ->
        WellTypedConfig prog env (ConfRestr c)
    | PAR : forall env1 env2 env c d,
        WellTypedConfig prog env1 c ->
        WellTypedConfig prog env2 d ->
        RuntimeEnvironmentCombination env1 env2 env ->
        WellTypedConfig prog env (ConfParallel c d)
    | MESSAGE : forall env v x m T,
        WellTypedTerm prog (map_maybe secondType env) (TValue v) T ->
        T ≤ ⌈ signature prog m ⌉ ->
        WellTypedConfig prog (insert x (TTMailbox (! « m »)) env) (ConfMessage x m v)
    | THREAD : forall env1 env2 env t T stack,
        env1 ▷ₑ env2 ~= (map_maybe returnType env) ->
        WellTypedTerm prog env1 t T ->
        WellTypedFrame prog env2 T stack ->
        WellTypedConfig prog env (ConfConf t stack)
    | SUBS : forall env env' c,
        RuntimeEnvironmentSubtype env env' ->
        WellTypedConfig prog env' c ->
        WellTypedConfig prog env c
  with WellTypedFrame (prog : Prog) : Env -> TUsage -> Stack -> Prop :=
    | EMPTY : forall T, WellTypedFrame prog [] T []
    | CONS : forall env1 env2 env t T1 T2 stack,
        WellTypedTerm prog (Some T1 :: env1) t T2 ->
        ReturnableType T2 ->
        WellTypedFrame prog env2 T2 stack ->
        env1 ▷ₑ env2 ~= env ->
        WellTypedFrame prog env T1 (t :: stack).

End runtime_def.

Notation "Env1 ⨝ₑ Env2 ~= Env" := (RuntimeEnvironmentCombination Env1 Env2 Env) (at level 80) : environment_scope.

Section runtime_props.
  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

  Lemma RuntimeSubtype_refl : forall T, RuntimeSubtype T T.
  Proof.
    destruct T; try destruct m; try constructor; apply MPInclusion_refl.
  Qed.

  Lemma RuntimeEnvironmentSubtype_refl : forall env, RuntimeEnvironmentSubtype env env.
  Proof.
    destruct env; constructor.
  Qed.

  Lemma RuntimeEnvironmentCombination_comm : forall env1 env2 env3,
    env1 ⨝ₑ env2 ~= env3 -> env2 ⨝ₑ env1 ~= env3.
  Proof.
    intros * Comb.
    induction Comb; try constructor; try apply IHComb.
    now apply TypeCombination_comm.
  Qed.

  Lemma RuntimeEnvironmentCombination_assoc : forall env1 env2 env3 env2' env,
    env1 ⨝ₑ env2' ~= env ->
    env2 ⨝ₑ env3 ~= env2' ->
    exists env1', env1' ⨝ₑ env3 ~= env /\ env1 ⨝ₑ env2 ~= env1'.
  Proof.
  Admitted.

  Lemma RuntimeEnvironmentCombination_Subtype_right : forall env1 env2 env2' env,
    env1 ⨝ₑ env2 ~= env ->
    RuntimeEnvironmentSubtype env2 env2' ->
    exists env', env1 ⨝ₑ env2' ~= env' /\ RuntimeEnvironmentSubtype env env'.
  Proof.
  Admitted.

  Lemma RuntimeEnvironmentCombination_Subtype : forall env1 env2 env env',
    env1 ⨝ₑ env2 ~= env ->
    RuntimeEnvironmentSubtype env env' ->
    exists env1' env2',
      env1' ⨝ₑ env2' ~= env' /\
      RuntimeEnvironmentSubtype env1 env1' /\
      RuntimeEnvironmentSubtype env2 env2'.
  Proof.
  Admitted.

  Lemma WellTypedConfig_exchange : forall x prog T c env,
    WellTypedConfig prog (insert x T (insert x T env)) c ->
    WellTypedConfig prog (insert x T (insert x T env)) (exchange_conf x c).
  Proof.
    intros * WT.
    remember (insert x T (insert x T env)) as E.
    revert x env T HeqE.
    induction WT; intros; inversion HeqE; subst; simpl in *.
    - assert (Eq : Some (TTMailbox (? 𝟙)) :: insert x T (insert x T env0) = insert (S x) T (insert (S x) T (Some (TTMailbox (? 𝟙)) :: env0))).
      {
        repeat rewrite raw_insert_successor.
        now repeat rewrite lookup_zero.
      }
      generalize (IHWT (S x) (Some (TTMailbox (? 𝟙)) :: env0) T Eq).
      intros WT'.
      now constructor.
    - econstructor.
      + eapply IHWT1. admit.
      + admit.
      + admit.
    - admit.
    - admit.
    - admit.
  Admitted.

  Lemma WellTypedConfig_PAR_inv : forall env c1 c2 prog,
    WellTypedConfig prog env (ConfParallel c1 c2) ->
    exists env1 env2,
      RuntimeEnvironmentCombination env1 env2 env /\
      WellTypedConfig prog env1 c1 /\ WellTypedConfig prog env2 c2.
  Proof.
    intros * WT.
    remember (ConfParallel c1 c2) as C.
    revert c1 c2 HeqC.
    induction WT; intros; inversion HeqC; subst.
    - now exists env1, env2.
    - generalize (IHWT _ _ eq_refl).
      intros [env1 [env2 [Comb [WT1 WT2]]]].
      eapply RuntimeEnvironmentCombination_Subtype with (env' := env) in Comb.
  Admitted.

  Lemma WellTypedConfig_lower : forall x c env prog,
    ~ In x (FV_conf c) ->
    WellTypedConfig prog (repeat None (S x) ++ env) c ->
    WellTypedConfig prog env (lower_conf x c).
  Proof.
    induction x; intros * In WT; simpl in *.
    - induction c; simpl in *.
      + admit.
      + admit.
      + eapply PAR.
        * apply IHc1.
          -- intros In'.
  Admitted.


  (*Lemma WellTypedConfig_lower : forall c env prog,*)
  (*  ~ In 0 (FV_conf c) ->*)
  (*  WellTypedConfig prog (None :: env) c ->*)
  (*  WellTypedConfig prog env (lower_conf 0 c).*)
  (*Proof.*)
  (*  intros * In WT.*)
  (*  remember (None :: env) as E.*)
  (*  revert env HeqE.*)
  (*  induction WT; intros; inversion HeqE; subst; simpl in *.*)
  (*  - apply NU.*)
  (**)
  (*  induction c; intros * In WT; simpl in *.*)
  (*  - admit.*)
  (*  - inversion WT; subst.*)
  (**)
  (**)
  (*  intros * WT.*)
  (**)
  (*  (*remember (None :: env) as E.*)*)
  (*  (*revert env HeqE.*)*)
  (*  (*induction WT; intros; inversion HeqE; subst.*)*)
  (*  induction WT.*)
  (*  - simpl in *.*)
  (*    apply NU.*)

  (*Lemma WellTypedConfig_lower : forall x c env prog,*)
  (*  WellTypedConfig prog (raw_insert (S x) None env) c ->*)
  (*  WellTypedConfig prog env (lower_conf x c).*)
  (*Proof.*)
  (*  intros x c.*)
  (*  revert x.*)
  (*  induction c; intros * WT; simpl in *.*)
  (*  - rewrite raw_insert_successor in WT.*)
  (*    destruct env.*)
  (*    + rewrite lookup_nil in WT; simpl in *.*)
  (*      admit.*)
  (*    + admit.*)
  (*  - eapply MESSAGE.*)


  Lemma preservation_equiv : forall prog env c d,
    WellTypedConfig prog env c ->
    StructCongr c d ->
    WellTypedConfig prog env d.
  Proof.
    intros * WTc Congr.
    revert env WTc.
    induction Congr; intros.
    - remember (ConfParallel c d) as C.
      revert c d HeqC.
      induction WTc; intros; inversion HeqC; subst.
      + eapply PAR; try eassumption.
        now apply RuntimeEnvironmentCombination_comm.
      + eapply SUBS; try eassumption.
        now apply IHWTc.
    - remember (ConfParallel c (ConfParallel d e)) as C.
      revert c d e HeqC.
      induction WTc; intros; inversion HeqC; subst.
      + remember (ConfParallel d0 e) as E'.
        revert env d0 e HeqE' H.
        clear IHWTc1 IHWTc2.
        induction WTc2; intros; inversion HeqE'; subst.
        * generalize (RuntimeEnvironmentCombination_assoc _ _ _ _ _ H0 H).
          intros [env' [Comb1 Comb2]].
          eapply PAR; try eapply PAR; eassumption.
        * generalize (RuntimeEnvironmentCombination_Subtype_right _ _ env' _ H0 H).
          intros [env'' [Comb' Sub']].
          eapply SUBS; try eassumption.
          apply IHWTc2; auto.
      + eapply SUBS; try eassumption.
        now apply IHWTc.
    - remember (ConfRestr (ConfRestr c)) as C.
      revert c HeqC.
      induction WTc; intros; inversion HeqC; subst.
      + do 2 apply NU.
        replace (Some (TTMailbox (? 𝟙)) :: Some (TTMailbox (? 𝟙)) :: env) with (insert 0 (TTMailbox (? 𝟙)) (insert 0 (TTMailbox (? 𝟙)) env)) by now repeat rewrite raw_insert_zero.
        apply WellTypedConfig_exchange.
        repeat rewrite raw_insert_zero.
        clear IHWTc HeqC.
        remember (ConfRestr c0) as C'.
        revert c0 HeqC'.
        induction WTc; intros; inversion HeqC'; subst.
        * easy.
        * eapply SUBS with (env' := Some (TTMailbox (? 𝟙)) :: env').
          -- constructor.
             apply RuntimeSubtype_refl.
             assumption.
          -- now apply IHWTc.
      + eapply SUBS; try eassumption.
        now apply IHWTc.
    - remember (ConfRestr (ConfParallel c d)) as C.
      revert c HeqC.
      induction WTc; intros; inversion HeqC; subst.
      + inversion WTc; subst.
        * inversion H5; subst.
          -- eapply PAR.
             ++ apply NU. apply H2.
             ++ admit.
             ++ apply H6.
          -- eapply PAR.
             ++ apply NU. admit.
             ++ admit.
             ++ apply H6.
          -- inversion H8; subst.
             ++ eapply PAR.
                ** apply NU.
                   admit.
                ** admit.
                ** admit.
             ++ admit.
        * admit.


      (**)
      (**)
      (*+ clear HeqC IHWTc.*)
      (*  remember (Some (TTMailbox (? 𝟙)) :: env) as E.*)
      (*  remember (ConfParallel c0 d) as C.*)
      (*  revert env c0 HeqC HeqE.*)
      (*  induction WTc; intros; inversion HeqC; subst.*)
      (*  * inversion H0; subst.*)
      (*    -- eapply PAR with (env1 := env3) (env2 := env4).*)
      (*       ++ now apply NU.*)
      (*       ++ admit.*)
      (*       ++ eassumption.*)
      (*    -- eapply PAR with (env2 := env4).*)
      (*       ++ apply NU.*)
      (*          eapply SUBS with (env' := None :: env3).*)
      (*          ** constructor; apply RuntimeEnvironmentSubtype_refl.*)
      (*          ** assumption.*)
      (*       ++ admit.*)
      (*       ++ eassumption.*)
      (*    -- inversion H6; subst.*)
      (*       ++ eapply PAR with (env1 := env3) (env2 := env4).*)
      (*          ** apply NU. admit.*)
      (*          ** admit.*)
      (*          ** assumption.*)
      (*       ++ eapply PAR with (env1 := env3) (env2 := env4).*)
      (*          ** apply NU. admit.*)
      (*          ** admit.*)
      (*          ** assumption.*)
      (*  * *)
      (**)
      (*    clear IHWTc H1.*)
      (*    remember (Some (TTMailbox (? 𝟙)) :: env0) as E.*)
      (*    remember (ConfParallel c0 d) as C.*)
      (*    revert env0 c0 HeqC HeqE.*)
      (*    induction WTc; intros; inversion HeqC; subst.*)
      (*    -- eapply PAR.*)

      + eapply SUBS; try eassumption.
        now apply IHWTc.
  Admitted.

  Theorem preservation : forall prog env c d,
    WellTypedProgram prog ->
    ReliableEnv env ->
    WellTypedConfig prog env c ->
    Step prog c d ->
    WellTypedConfig prog env d.
  Proof.
    intros * WTP Reliable WT Step.
    revert env Reliable WT.
    induction Step; intros.
    - inversion WT; subst.
      + inversion H3; subst.
        * generalize (EnvironmentCombination_assoc).
          econstructor.
          -- admit.
          -- apply H6.
          --


    induction WT; intros * Reliable Step.
    - admit.
    - inversion Step; subst.
      + admit.
      + eapply PAR.
        * eapply IHWT1.
          admit. (* Need new lemma *)
          assumption.
        * eapply IHWT2.
          admit. (* Need new lemma *)
          admit.

End runtime_props.
