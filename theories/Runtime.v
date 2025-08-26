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


  Definition Frame := (VarName * Term)%type.

(**
    A stack is a simply a list of terms. Due to the usage of deBruijn indices
   we don't include variable names in frames.
    We will always replace variable 0.
  *)
  (*Definition Stack := list Term.*)
  Definition Stack := list Frame.

  Definition lift_Frame (f : Frame) :=
    match f with
    | (x, t) => (S x, lift 1 0 t)
    end.

  (*Definition lift_Stack (s : Stack) := map (lift 1 0) s.*)
  Definition lift_Stack (s : Stack) := map lift_Frame s.

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

  Fixpoint exchange_Stack (i : VarName) (s : Stack) : Stack :=
    match s with
    | [] => []
    | (x, t) :: s' => (exchange_Var i x, exchange i t) :: exchange_Stack i s'
    end.

  Fixpoint exchange_conf (i : VarName) (c : Configuration) : Configuration :=
    match c with
    | ConfConf t s => ConfConf (exchange i t) (exchange_Stack i s)
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
        StructCongr (ConfRestr (ConfParallel c d)) (ConfParallel (ConfRestr c) (lower_conf 0 d)).

  Inductive RecTree : Type :=
    | zero : RecTree
    | one : RecTree -> RecTree
    | two : RecTree -> RecTree -> RecTree.

  Inductive StructEq : Configuration -> RecTree -> Configuration -> Prop :=
    | stop : forall c d, StructCongr c d -> StructEq c zero d
    (* Properties of equivalence relation *)
    | CongrRefl : forall c, StructEq c zero c
    | CongrSym : forall c d r, StructEq c r d -> StructEq d (one r) c
    | CongrTrans : forall c d e r p, StructEq c r d -> StructEq d p e -> StructEq c (two r p) e
    (* Properties of congruence relation, i.e. congruence under a context *)
    | CongrNu : forall c c' r, StructEq c r c' -> StructEq (ConfRestr c) (one r) (ConfRestr c')
    | CongrPar : forall c c' d r, StructEq c r c' -> StructEq (ConfParallel c d) (one r) (ConfParallel c' d).

  Inductive Step (prog : Prog) : Configuration -> Configuration -> Prop :=
    | stepLet : forall t1 t2 stack,
        Step prog (ConfConf (TLet t1 t2) stack) (ConfConf t1 ((0, t2) :: stack))
    | stepReturn : forall (v : Value) x t stack,
        Step prog (ConfConf (TValue v) ((x, t) :: stack)) (ConfConf (subst v x t) stack)
    | stepApp : forall v stack definition bodyType argumentType t,
        definitions prog definition = (FunDef definition argumentType bodyType t) ->
        Step prog (ConfConf (TApp definition v) stack) (ConfConf (subst v 0 t) stack)
    | stepNew : forall stack,
        Step prog (ConfConf TNew stack) (ConfRestr (ConfConf (TValue (ValueVar 0)) (lift_Stack stack)))
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
    | stepStruct : forall r c c' d d',
        StructEq c r c' ->
        StructEq d' r d ->
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
        Unrestricted (⌈ T ⌉) ->
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

  Inductive WellTypedStack (prog : Prog) : Env -> TUsage -> Stack -> Prop :=
    | EMPTY : forall env T, EmptyEnv env -> WellTypedStack prog env T []
    | CONS : forall x env1 env2 env t T1 T2 stack,
        WellTypedTerm prog (insert x T1 env1) t T2 ->
        ReturnableType T2 ->
        WellTypedStack prog env2 T2 stack ->
        env1 ▷ₑ env2 ~= env ->
        WellTypedStack prog env T1 ((x, t) :: stack).

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
        WellTypedStack prog env2 T stack ->
        WellTypedConfig prog env (ConfConf t stack)
    | SUBS : forall env env' c,
        RuntimeEnvironmentSubtype env env' ->
        WellTypedConfig prog env' c ->
        WellTypedConfig prog env c.

End runtime_def.

Notation "Env1 ⨝ₑ Env2 ~= Env" := (RuntimeEnvironmentCombination Env1 Env2 Env) (at level 80) : environment_scope.

Section runtime_props.
  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

  Lemma RuntimeSubtype_refl : forall T, RuntimeSubtype T T.
  Proof.
    destruct T; try destruct m; try constructor; apply MPInclusion_refl.
  Qed.

  Lemma RuntimeSubtype_trans : forall T1 T2 T3,
    RuntimeSubtype T1 T2 ->
    RuntimeSubtype T2 T3 ->
    RuntimeSubtype T1 T3.
  Proof.
    intros * Sub1 Sub2.
    inversion Sub1; subst; inversion Sub2; subst;
    constructor; eapply MPInclusion_trans; eassumption.
  Qed.

  Lemma RuntimeEnvironmentSubtype_refl : forall env, RuntimeEnvironmentSubtype env env.
  Proof.
    destruct env; constructor.
  Qed.

  Lemma RuntimeEnvironmentSubtype_trans : forall env1 env2 env3,
    RuntimeEnvironmentSubtype env1 env2 ->
    RuntimeEnvironmentSubtype env2 env3 ->
    RuntimeEnvironmentSubtype env1 env3.
  Proof.
  Admitted.

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

  (*Lemma ConfMessage_exchange : forall x y prog v env env' m T1 T2,*)
  (*  insert x (TTMailbox (! « m »)) env = insert y T1 (insert y T1 env') ->*)
  (*  WellTypedTerm prog (map_maybe secondType env) (TValue v) T2 ->*)
  (*  T2 ≤ ⌈ signature prog m ⌉ ->*)
  (*  WellTypedConfig prog (insert x (TTMailbox (! « m »)) env) (ConfMessage (exchange_Var y x) m (exchange_Value y v)).*)
  (*Proof.*)
  (*  intros * Eq WT2 Sub.*)
  (*  rewrite insert_insert in Eq by reflexivity.*)
  (*  rewrite Eq.*)
  (*  destruct v.*)
  (*  + admit.*)
  (*  + admit.*)
  (*  + simpl.*)
  (*    unfold exchange_Var.*)
  (*    destruct (Nat.eq_dec x y); destruct (Nat.eq_dec v y).*)
  (*    * subst.*)
  (*      apply MESSAGE.*)
  (*      rewrite raw_insert_successor.*)
  (*  unfold exchange_Value.*)
  (*  Print MESSAGE.*)
  (*  constructor.*)
  (*Admitted.*)

  (*Lemma WellTypedConfig_exchange : forall x prog T c env,*)
  (*  WellTypedConfig prog (insert x T (insert x T env)) c ->*)
  (*  WellTypedConfig prog (insert x T (insert x T env)) (exchange_conf x c).*)
  (*Proof.*)
  (*  intros * WT.*)
  (*  remember (insert x T (insert x T env)) as E.*)
  (*  revert x env T HeqE.*)
  (*  induction WT; intros; inversion HeqE; subst; simpl in *.*)
  (*  - assert (Eq : Some (TTMailbox (? 𝟙)) :: insert x T (insert x T env0) = insert (S x) T (insert (S x) T (Some (TTMailbox (? 𝟙)) :: env0))).*)
  (*    {*)
  (*      repeat rewrite raw_insert_successor.*)
  (*      now repeat rewrite lookup_zero.*)
  (*    }*)
  (*    generalize (IHWT (S x) (Some (TTMailbox (? 𝟙)) :: env0) T Eq).*)
  (*    intros WT'.*)
  (*    now constructor.*)
  (*  - admit.*)
  (*  - rewrite HeqE.*)
  (*    unfold exchange_Var.*)
  (*    destruct (PeanoNat.Nat.eq_dec x0 x).*)
  (*    + replace (if Nat.eq_dec x x0 then S x else if x =? S x0 then x0 else x) with (S x).*)
  (*      * subst.*)
  (*        generalize (insert_eq_insert_1 _ _ _ _ _ HeqE).*)
  (*        intros; subst.*)
  (*        rewrite HeqE.*)
  (*        rewrite insert_insert by reflexivity.*)
  (*        eapply MESSAGE with (T := T).*)
  (*        -- destruct v; simpl.*)
  (*           ++ generalize (canonical_form_BTBool _ _ _ _ H).*)
  (*              intros ->.*)
  (*              inversion H0; subst.*)
  (*              (* Impossible due to TUBase BTBool ≤ ⌈ signature prog m ⌉*)*)
  (*              admit.*)
  (*           ++ admit.*)
  (*           ++ unfold exchange_Var.*)
  (*              destruct (PeanoNat.Nat.eq_dec v x).*)
  (*              ** subst.*)
  (*                 (* Should be possible to prove *)*)
  (*                 admit.*)
  (*              ** destruct (v =? (S x)).*)
  (*                 --- admit.*)
  (*                 --- Search (insert _ _ _).*)
  (**)
  (*      admit.*)
  (*      subst. simpl.*)
  (*      destruct (Nat.eq_dec x x).*)
  (*      * reflexivity.*)
  (*      * exfalso; apply n; reflexivity.*)
  (*      subst. simpl.*)
  (*    +*)
  (*  - admit.*)
  (*  - admit.*)
  (*Admitted.*)

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

  Lemma Par_comm : forall prog env c d,
    WellTypedConfig prog env (ConfParallel c d) ->
    WellTypedConfig prog env (ConfParallel d c).
  Proof.
    intros * WT.
    remember (ConfParallel c d) as C.
    revert c d HeqC.
    induction WT; intros; inversion HeqC; subst.
    + eapply PAR; try eassumption.
      now apply RuntimeEnvironmentCombination_comm.
    + eapply SUBS; try eassumption; now apply IHWT.
  Qed.

  Lemma Par_assoc : forall prog env c d e,
    WellTypedConfig prog env (ConfParallel c (ConfParallel d e)) ->
    WellTypedConfig prog env (ConfParallel (ConfParallel c d) e).
  Proof.
    intros * WT.
    remember (ConfParallel c (ConfParallel d e)) as C.
    revert c d e HeqC.
    induction WT; intros; inversion HeqC; subst.
    + remember (ConfParallel d0 e) as E'.
      revert env d0 e HeqE' H.
      clear IHWT1 IHWT2.
      induction WT2; intros; inversion HeqE'; subst.
      * generalize (RuntimeEnvironmentCombination_assoc _ _ _ _ _ H0 H).
        intros [env' [Comb1 Comb2]].
        eapply PAR; try eapply PAR; eassumption.
      * generalize (RuntimeEnvironmentCombination_Subtype_right env1 env env' env0 H0 H).
        intros [env'' [Comb' Sub']].
        eapply SUBS; try eassumption.
        apply IHWT2; auto.
    + eapply SUBS; try eassumption; now apply IHWT.
  Qed.

  Lemma WellTypedConfig_ConfRestr_inv : forall prog env c,
    WellTypedConfig prog env (ConfRestr c) ->
    exists env', RuntimeEnvironmentSubtype env env' /\
      WellTypedConfig prog (Some (TTMailbox (? 𝟙)) :: env') c.
  Proof.
    intros * WT.
    remember (ConfRestr c) as C.
    revert c HeqC.
    induction WT; intros; inversion HeqC; subst.
    - exists env; split.
      + apply RuntimeEnvironmentSubtype_refl.
      + assumption.
    - generalize (IHWT c0 eq_refl).
      intros [env'' [Sub' WT']].
      exists env''; split.
      + eapply RuntimeEnvironmentSubtype_trans; eassumption.
      + assumption.
  Qed.

  Lemma WellTypedConfig_ConfRestr_inv' : forall prog env c,
    WellTypedConfig prog env (ConfRestr c) ->
    WellTypedConfig prog (Some (TTMailbox (? 𝟙)) :: env) c \/
    exists env', RuntimeEnvironmentSubtype env env' /\
      WellTypedConfig prog env' c.
  Proof.
    intros * WT.
    remember (ConfRestr c) as C.
    revert c HeqC.
    induction WT; intros; inversion HeqC; subst.
    - now left.
    - generalize (IHWT c0 eq_refl).
      intros [WT' | [env'' [Sub' WT']]].
      + left. eapply SUBS with (env' := Some (TTMailbox (? 𝟙)) :: env').
        * constructor; (apply RuntimeSubtype_refl || assumption).
        * assumption.
      + right; exists env''; eauto using RuntimeEnvironmentSubtype_trans.
  Qed.

  Lemma WellTypedConfig_ConfRestr_inv'' : forall prog env c,
    WellTypedConfig prog env (ConfRestr c) ->
    WellTypedConfig prog (Some (TTMailbox (? 𝟙)) :: env) c.
  Proof.
    intros * WT.
    remember (ConfRestr c) as C.
    revert c HeqC.
    induction WT; intros; inversion HeqC; subst.
    - assumption.
    - generalize (IHWT _ eq_refl).
      intros WT'.
      eapply SUBS with (env' := Some (TTMailbox (? 𝟙)) :: env').
      + constructor; auto using RuntimeSubtype_refl.
      + assumption.
  Qed.

  Lemma WellTypedConfig_ConfConf_inv : forall prog env t stack,
    WellTypedConfig prog env (ConfConf t stack) ->
    exists env' T env1 env2,
      env1 ▷ₑ env2 ~= map_maybe returnType env' /\
      WellTypedTerm prog env1 t T /\
      WellTypedStack prog env2 T stack /\
      RuntimeEnvironmentSubtype env env'.
  Proof.
    intros * WT.
    remember (ConfConf t stack) as C.
    revert t stack HeqC.
    induction WT; intros; inversion HeqC; subst.
    - exists env, T, env1, env2; repeat split; try assumption.
      apply RuntimeEnvironmentSubtype_refl.
    - generalize (IHWT _ _ eq_refl).
      intros [envT [T [env1 [env2 [Comb [WT1 [WT2 Sub]]]]]]].
      exists envT, T, env1, env2; repeat split; try assumption.
      eapply RuntimeEnvironmentSubtype_trans; eassumption.
  Qed.

  Lemma WellTypedConfig_ConfConf_inv' : forall prog env t stack,
    WellTypedConfig prog env (ConfConf t stack) ->
    (exists T env1 env2,
      env1 ▷ₑ env2 ~= map_maybe returnType env /\
      WellTypedTerm prog env1 t T /\
      WellTypedStack prog env2 T stack) \/
    (exists env', RuntimeEnvironmentSubtype env env' /\
      WellTypedConfig prog env' (ConfConf t stack)).
  Proof.
    intros * WT.
    remember (ConfConf t stack) as C.
    revert t stack HeqC.
    induction WT; intros; inversion HeqC; subst.
    - left; exists T, env1, env2; repeat split; try assumption.
    - generalize (IHWT _ _ eq_refl).
      intros [[T [env1 [env2 [Comb [WT1 WT2]]]]] | [env'' [Sub WT']]].
      + right; exists env'; split.
        * assumption.
        * econstructor; eassumption.
      + right; exists env'; split.
        * eauto using RuntimeEnvironmentSubtype_trans.
        * eapply SUBS; eassumption.
  Qed.

  Lemma RuntimeEnvironmentSubtype_None_inv : forall env1 env2,
    RuntimeEnvironmentSubtype (None :: env1) env2 ->
    exists env2',
      RuntimeEnvironmentSubtype env1 env2' /\ env2 = None :: env2'.
  Proof.
    intros * Sub.
    remember (None :: env1) as E.
    revert env1 HeqE.
    induction Sub; intros; inversion HeqE; subst.
    - exists env2; auto.
    - generalize (IHSub1 _ eq_refl).
      intros [env2' [Sub' ->]].
      generalize (IHSub2 _ eq_refl).
      intros [env2'' [Sub'' ->]].
      exists env2''; eauto using RuntimeEnvironmentSubtype_trans.
    - exists env1; eauto using RuntimeEnvironmentSubtype_refl.
  Qed.

  Lemma RuntimeEnvironmentSubtype_Some_inv : forall env1 env2 T,
    RuntimeEnvironmentSubtype (Some T :: env1) env2 ->
    exists env2',
      RuntimeEnvironmentSubtype env1 env2' /\
      (env2 = None :: env2' \/
      exists T', RuntimeSubtype T T' /\ env2 = Some T' :: env2').
  Proof.
    intros * Sub.
    remember (Some T :: env1) as E.
    revert T env1 HeqE.
    induction Sub; intros; inversion HeqE; subst.
    - exists env2; auto.
    - exists env2; split.
      + assumption.
      + right; exists T2; auto.
    - generalize (IHSub1 _ _ eq_refl).
      intros [env2' [Sub' [-> | [T' [SubT' ->]]]]].
      + apply RuntimeEnvironmentSubtype_None_inv in Sub2.
        destruct Sub2 as [env2'' [Sub'' ->]].
        exists env2''; split.
        * eauto using RuntimeEnvironmentSubtype_trans.
        * now left.
      + generalize (IHSub2 _ _ eq_refl).
        intros [env2'' [Sub'' [-> | [T'' [SubT'' ->]]]]].
        exists env2''; split.
        * eauto using RuntimeEnvironmentSubtype_trans.
        * now left.
        * exists env2''; split.
          -- eauto using RuntimeEnvironmentSubtype_trans.
          -- right; exists T''; eauto using RuntimeSubtype_trans.
    - exists env1; split.
      + apply RuntimeEnvironmentSubtype_refl.
      + right; exists T; auto using RuntimeSubtype_refl.
  Qed.

  Lemma asdveasf : forall env1 env2,
    RuntimeEnvironmentSubtype (Some (TTMailbox (? 𝟙)) :: Some (TTMailbox (? 𝟙)) :: env1) env2 ->
    exists env2' T1 T2,
      env2 = Some T1 :: Some T2 :: env2' /\
      RuntimeSubtype (TTMailbox (? 𝟙)) T1 /\
      RuntimeSubtype (TTMailbox (? 𝟙)) T2 /\
      RuntimeEnvironmentSubtype env1 env2'.
  Proof.
    intros * Sub.
    remember (Some (TTMailbox (? 𝟙)) :: Some (TTMailbox (? 𝟙)) :: env1) as E1.
    revert env1 HeqE1.
    induction Sub; intros; inversion HeqE1; subst.
    - inversion H.
    - clear IHSub HeqE1.
      remember (Some (TTMailbox (? 𝟙)) :: env0) as E0.
      revert env0 HeqE0.
      induction Sub; intros; inversion HeqE0; subst.
      + inversion H0.
      + exists env2, T2, T0; eauto.
      + generalize (IHSub1 _ eq_refl).
        intros [env2' [T1 [T3 [Eq [SubT1 [SubT2 Sub]]]]]].
        eapply IHSub2. inversion Eq; subst.
  Admitted.

  Lemma sacfewf : forall env1 env2,
    RuntimeEnvironmentSubtype (Some (TTMailbox (? 𝟙)) :: Some (TTMailbox (? 𝟙)) :: env1) env2 ->
    exists env2',
      RuntimeEnvironmentSubtype (Some (TTMailbox (? 𝟙)) :: Some (TTMailbox (? 𝟙)) :: env1) (Some (TTMailbox (? 𝟙)) :: Some (TTMailbox (? 𝟙)) :: env2').
  Proof.
    intros * Sub.
    remember (Some (TTMailbox (? 𝟙)) :: Some (TTMailbox (? 𝟙)) :: env1) as E1.
    revert env1 HeqE1.
    induction Sub; intros; inversion HeqE1; subst.
    - inversion H.
    - exists env0; repeat constructor; auto using MPInclusion_refl.
    - exists env0; repeat constructor; auto using MPInclusion_refl.
    - exists env1; repeat constructor; auto using MPInclusion_refl.
  Qed.

  Lemma asvaefe : forall x T env1 env2,
    RuntimeEnvironmentSubtype (raw_insert x T (raw_insert x T env1)) env2 ->
    exists T1 T2 env2',
      env2 = raw_insert x T1 (raw_insert x T2 env2').
  Proof.
    induction x; intros * Sub.
    - repeat rewrite raw_insert_zero in *.
      repeat setoid_rewrite raw_insert_zero.
      destruct env2.
      + admit. (* Impossible *)
      + destruct env2.
        * admit. (* Impossible *)
        * eauto.
    - admit.
  Admitted.

  (*Lemma asvaefeasdf : forall x T env1 env2,*)
  (*  RuntimeEnvironmentSubtype (raw_insert x T (raw_insert x T env1)) env2 ->*)
  (*  exists T1 T2 env2',*)
  (*    env2 = raw_insert x T1 (raw_insert x T2 env2') /\*)
  (*    RuntimeSubtype T T1 /\*)
  (*    RuntimeSubtype T T2.*)
  (*Proof.*)
  (*  induction x; intros * Sub.*)
  (*  - repeat rewrite raw_insert_zero in *.*)
  (*    repeat setoid_rewrite raw_insert_zero.*)
  (*    destruct env2.*)
  (*    + admit. (* Impossible *)*)
  (*    + destruct env2.*)
  (*      * admit. (* Impossible *)*)
  (*      * eauto.*)
  (*  - admit.*)
  (*Admitted.*)

  Lemma common_superpattern : forall e f1 f2,
    e ⊑ f1 ->
    e ⊑ f2 ->
    f1 ⊑ f1 ⊕ f2 /\ f2 ⊑ f1 ⊕ f2.
  Proof.
    intros * Inc1 Inc2; split.
    - intros m mIn; now constructor.
    - intros m mIn; now constructor.
  Qed.

  (*Lemma contra_zero : forall f,*)
  (*  ~ f ≈ 𝟘 -> exists mc, mc ∈ f.*)
  (*Proof.*)
  (*  induction f; intros Neg;*)
  (*  try (eexists; constructor; fail).*)
  (*  - exfalso; now apply Neg.*)
  (*  - assert (~ f1 ≈ 𝟘 \/ ~ f2 ≈ 𝟘).*)
  (*    {*)
  (*      Search (_ ≈ 𝟘).*)
  (*      inversion Neg.*)
  (*      intros Eq.*)
  (*      inversion Eq.*)
  (*      apply Neg.*)
  (*      constructor.*)
  (*      - intros m mIn.*)
  (*        inversion mIn; subst.*)
  (*        + now apply H.*)
  (*        + *)
  (**)
  (*      inversion Eq.*)
  (*    }*)

  (*Lemma contra_zero : forall f,*)
  (*  f <> 𝟘 -> f ⊑ 𝟘 -> False.*)
  (*Proof.*)
  (*  intros * Neg Inc.*)
  (*  induction f.*)
  (*  - now apply Neg.*)
  (*  - assert (⟨⟩ ∈ 𝟙) by constructor.*)
  (*    generalize (Inc ⟨⟩ H); intros C; inversion C.*)
  (*  - assert (⟨ m ⟩ ∈ « m ») by constructor.*)
  (*    generalize (Inc ⟨ m ⟩ H); intros C; inversion C.*)
  (*  - *)

  (*Lemma common_subpattern : forall e f1 f2,*)
  (*  f1 ⊑ e ->*)
  (*  f2 ⊑ e ->*)
  (*  exists e', ~ e' ⊑ 𝟘 /\ e' ⊑ f1 /\ e' ⊑ f2.*)
  (*Proof.*)
  (*  induction e, f1; intros * Inc1 Inc2.*)
  (*  - *)

  (* TODO: This is not a good lemma *)
  Lemma common_subpattern : forall e f1 f2,
    f1 ⊑ e ->
    f2 ⊑ e ->
    exists e', e' ⊑ f1 /\ e' ⊑ f2.
  Proof.
    intros * Inc1 Inc2; exists 𝟘; split; intros m' mIn; inversion mIn.
  Qed.

  Lemma MPInclusion_zero : forall e, 𝟘 ⊑ e.
  Proof.
    intros e; intros m mIn; inversion mIn.
  Qed.

  (*Lemma valueOf_dec : forall e mb, {mb ∈ e} + {~ mb ∈ e}.*)
  (*Proof.*)
  (*  Ltac impossible := right; intros In; inversion In.*)
  (*  induction e; intros *.*)
  (*  - impossible.*)
  (*  - destruct mb.*)
  (*    + left; constructor.*)
  (*    + impossible.*)
  (*  - destruct mb.*)
  (*    + impossible.*)
  (*    + destruct (Message.eq_dec m0 m).*)
  (*      * subst. destruct mb.*)
  (*        -- left; constructor.*)
  (*        -- impossible.*)
  (*      * impossible; subst; now apply n.*)
  (*  - generalize (IHe1 mb); generalize (IHe2 mb).*)
  (*    intros In1 In2.*)
  (*    destruct In1, In2; try (left; now constructor).*)
  (*    impossible; subst; auto.*)
  (*  - destruct mb.*)
  (*    + generalize (IHe1 []); generalize (IHe2 []).*)
  (*      intros In1 In2; destruct In1, In2.*)
  (*      * left; econstructor; try eassumption; constructor.*)
  (*      * right; intros In. inversion In; subst.*)
  (*        apply mailbox_union_empty in H4; destruct H4; subst.*)
  (*        now apply n.*)
  (*      * right; intros In. inversion In; subst.*)
  (*        apply mailbox_union_empty in H4; destruct H4; subst.*)
  (*        now apply n.*)
  (*      * right; intros In. inversion In; subst.*)
  (*        apply mailbox_union_empty in H4; destruct H4; subst.*)
  (*        now apply n.*)
  (*    + generalize (IHe1 [m]); generalize (IHe2 [m]); generalize (IHe1 mb); generalize (IHe2 mb).*)
  (*      intros In1 In2 In3 In4.*)
  (*      destruct In1, In2, In3, In4.*)
  (*      * left; econstructor.*)
  (*        apply v2.*)
  (*        apply v.*)
  (*        now constructor.*)
  (*      * left; econstructor.*)
  (*        apply v0.*)
  (*        apply v1.*)
  (*        rewrite mailbox_union_comm; now constructor.*)
  (*      * left; econstructor.*)
  (*        apply v1.*)
  (*        apply v.*)
  (*        now constructor.*)
  (*      * right; intros In; inversion In; subst.*)
  (*        admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*      * admit.*)
  (*  - induction mb.*)
  (*    + left; constructor; exists 0; simpl; constructor.*)
  (*    + destruct IHmb.*)
  (*      * generalize (IHe [a]); intros [ In | In ].*)
  (*        -- left; constructor.*)
  (*           inversion v; subst; destruct H1.*)
  (*           exists (S x); simpl.*)
  (*           econstructor; now try eassumption.*)
  (*        -- right; intros In'.*)
  (*           inversion In'; subst; destruct H1.*)
  (*           destruct x.*)
  (*           ++ simpl in *; inversion H.*)
  (*           ++ simpl in *; inversion H; subst.*)
  (*              admit. *)
  (*      * generalize (IHe [a]); intros [ In | In ].*)
  (*        -- *)
  (*      * left.*)
  (**)
  (**)
  (*    Search (⋆ _).*)
  (*    generalize (IHe mb).*)
  (*    intros [In | In].*)
  (*    + left; constructor; exists 1. simpl.*)
  (*      now rewrite MPComp_unit.*)
  (*    + revert e IHe In.*)
  (*      induction mb; intros.*)
  (*      * left; constructor; exists 0; simpl; constructor.*)
  (*      * *)
  (**)
  (*      right; intros In'.*)
  (*      inversion In'; subst.*)
  (*      destruct H1.*)
  (*      Search (_ ∈ ⋆ _).*)

  Lemma MPInclusion_dec : forall e f, {e ⊑ f} + {~ e ⊑ f}.
  Proof.
    induction e; induction f;
    try (now left).
    - right; intros Eq.
      assert (In : ⟨⟩ ∈ 𝟙) by constructor.
      generalize (Eq _ In); intros C; inversion C.
    - right; intros Eq.
      assert (In : ⟨⟩ ∈ 𝟙) by constructor.
      generalize (Eq _ In); intros C; inversion C.
    - destruct IHf1, IHf2.
      + left; intros m' In.
        inversion In; subst.
        constructor.
        now apply m.
      + left; intros m' In.
        inversion In; subst.
        constructor.
        now apply m.
      + left; intros m' In.
        inversion In; subst.
        apply MPValueChoiceRight.
        now apply m.
      + right.
        intros Inc.
        assert (In : ⟨⟩ ∈ 𝟙) by constructor.
        generalize (Inc _ In).
        intros.
        inversion H; subst.
        * apply n; intros m' mIn; inversion mIn; now subst.
        * apply n0; intros m' mIn; inversion mIn; now subst.
    - destruct IHf1, IHf2;
      try (
        right; intros Inc;
        assert (In : ⟨⟩ ∈ 𝟙) by constructor; generalize (Inc _ In); intros InC; inversion InC; subst;
        apply mailbox_union_empty in H4; destruct H4; subst;
        apply n; intros m' In'; now inversion In'; subst
      ).
      left; intros m' mIn.
      inversion mIn; subst.
      econstructor.
      + apply m; eassumption.
      + apply m0; eassumption.
      + constructor.
    - left. intros m mIn. constructor. now exists 0.
    - right. intros Inc.
      assert (⟨ m ⟩ ∈ « m ») by constructor.
      generalize (Inc ⟨ m ⟩ H); intros C; inversion C.
    - right. intros Inc.
      assert (⟨ m ⟩ ∈ « m ») by constructor.
      generalize (Inc ⟨ m ⟩ H); intros C; inversion C.
    - destruct (Message.eq_dec m m0).
      + subst; now left.
      + right.
        intros Inc.
        assert (⟨ m ⟩ ∈ « m ») by constructor.
        generalize (Inc ⟨ m ⟩ H); intros C; inversion C; subst.
        now exfalso.
    - destruct IHf1, IHf2;
      try(
        left; intros m' mIn; inversion mIn; subst;
        constructor; now apply m0
      ).
      right. intros Inc.
      assert (⟨ m ⟩ ∈ « m ») by constructor.
      generalize (Inc ⟨ m ⟩ H); intros C; inversion C; subst.
      + apply n; intros m' mIn; inversion mIn; now subst.
      + apply n0; intros m' mIn; inversion mIn; now subst.
    - destruct IHf1, IHf2.
      + right; intros Inc.
        assert (⟨ m ⟩ ∈ « m ») by constructor.
        generalize (Inc ⟨ m ⟩ H); intros C; inversion C; subst.
        assert (Eq : ⟨ m ⟩ ⊎ ⟨⟩ =ᵐᵇ a ⊎ b) by (rewrite mailbox_union_comm; now rewrite <- mailbox_union_empty_left).
        generalize (mailbox_eq_union_split m ⟨⟩ a b Eq).
        intros [[a' EqA] | [b' EqB]].
        * rewrite <- mailbox_union_assoc in EqA.
          apply Permutation.Permutation_app_inv_l in EqA.
          apply mailbox_union_empty in EqA; destruct EqA as [-> ->].
          rewrite <- mailbox_union_empty_right in H5.
          rewrite <- H5 in H2.
          generalize (m1 _ H). intros.
          admit.
        * admit.
      + admit.
      + admit.
      + admit.
    - destruct IHf.
      + left; constructor. exists 1. econstructor.
        * apply m0; eassumption.
        * constructor.
        * apply mailbox_union_empty_right.
      + right. intros Inc.
        apply n.
        intros m' mIn; inversion mIn; subst.
        generalize (Inc _ mIn).
        intros InStar.
        inversion InStar; subst.
        destruct H1 as [x Pow].
        inversion Pow; subst.
        * 
  Admitted.


  Lemma MPEqual_dec : forall e f, {e ≈ f} + {~ e ≈ f}.
  Proof.
    intros *.
    destruct (MPInclusion_dec e f), (MPInclusion_dec f e).
    - now left.
    - right; now intros [N1 N2].
    - right; now intros [N1 N2].
    - right; now intros [N1 N2].
  Qed.

  (*Lemma sdfesadsf : forall e,*)
  (*  ~ e ≈ 𝟘 ->*)
  (*  exists mc, mc ∈ e.*)
  (*Proof.*)
  (*  induction e; intros Neg.*)
  (*  - exfalso; now apply Neg.*)
  (*  - eexists; constructor.*)
  (*  - eexists; constructor.*)
  (*  - eexists. unfold "≈" in Neg.*)
  (*    Search (~ (_ /\ _)).*)
  (*    assert (~ e1 ≈ 𝟘 \/ ~ e2 ≈ 𝟘).*)
  (*    {*)
  (*      split.*)
  (*      - intros Eq.*)
  (*        rewrite Eq in Neg.*)
  (*        rewrite MPChoice_comm in Neg.*)
  (*        rewrite MPChoice_unit in Neg.*)
  (*        generalize (IHe2 Neg).*)
  (*        intros [mc In].*)
  (**)
  (*    }*)
  (**)
  (**)
  (**)
  (*Lemma PatternEq_zero : forall e, {e ≈ 𝟘} + {~ e ≈ 𝟘}.*)
  (*Proof.*)
  (*  induction e.*)
  (*  - now left.*)
  (*  - right; intros Eq; inversion Eq.*)
  (*    assert (In : ⟨⟩ ∈ 𝟙) by constructor.*)
  (*    generalize (H ⟨⟩ In); intros C; inversion C.*)
  (*  - right; intros Eq; inversion Eq.*)
  (*    assert (In : ⟨ m ⟩ ∈ « m ») by constructor.*)
  (*    generalize (H ⟨ m ⟩ In); intros C; inversion C.*)
  (*  - destruct IHe1, IHe2.*)
  (*    + left. constructor.*)
  (*      * intros m' mIn.*)
  (*        inversion mIn; subst.*)
  (*        -- now rewrite m in H1.*)
  (*        -- now rewrite m0 in H1.*)
  (*      * apply MPInclusion_zero.*)
  (*    + right; intros Eq.*)
  (*      rewrite m in Eq; rewrite MPChoice_comm in Eq; rewrite MPChoice_unit in Eq.*)
  (*      auto.*)
  (*    + right; intros Eq.*)
  (*      rewrite m in Eq; rewrite MPChoice_unit in Eq.*)
  (*      auto.*)
  (*    + right; intros Eq.*)
  (*      inversion Eq.*)

      

  Lemma MPInclusion_one : forall e, e ⊑ 𝟙 -> e ⊑ 𝟘 \/ 𝟙 ⊑ e.
  Proof.
    induction e; intros Inc.
    - now left.
    - now right.
    - assert (⟨ m ⟩ ∈ « m ») by constructor.
      generalize (Inc ⟨ m ⟩ H); intros C; inversion C.
    - Search (_ ⊑ _).
    Admitted.

  Lemma MPInclusion_one' : forall e, e ⊑ 𝟙 -> e ⊑ 𝟘 \/ 𝟙 ⊑ e.
  Proof.
    induction e; intros Inc.
    - left; apply MPInclusion_refl.
    - right; apply MPInclusion_refl.
    - assert (⟨ m ⟩ ∈ « m ») by constructor.
      generalize (Inc ⟨ m ⟩ H); intros C; inversion C.
    - destruct (MPInclusion_dec e1 𝟙), (MPInclusion_dec e2 𝟙).
      + generalize (IHe1 m); intros [Inc1_0 | Inc1_1];
        generalize (IHe2 m0); intros [Inc2_0 | Inc2_1].
        * left. intros m' mIn; inversion mIn; subst.
          -- now apply Inc1_0.
          -- now apply Inc2_0.
        * right; intros m' mIn; inversion mIn; subst.
          apply MPValueChoiceRight; now apply Inc2_1.
        * right; intros m' mIn; inversion mIn; subst.
          apply MPValueChoiceLeft; now apply Inc1_1.
        * right; intros m' mIn; inversion mIn; subst.
          apply MPValueChoiceLeft; now apply Inc1_1.
      + exfalso; apply n; intros m' mIn.
        apply Inc; now apply MPValueChoiceRight.
      + exfalso; apply n; intros m' mIn.
        apply Inc; now apply MPValueChoiceLeft.
      + exfalso; apply n; intros m' mIn.
        apply Inc; now apply MPValueChoiceLeft.
    - destruct (MPInclusion_dec e1 𝟙), (MPInclusion_dec e2 𝟙).
      + generalize (IHe1 m); intros [Inc1_0 | Inc1_1];
        generalize (IHe2 m0); intros [Inc2_0 | Inc2_1].
        * left; intros m' mIn; inversion mIn; subst.
          generalize (Inc1_0 _ H1); intros.
          inversion H.
        * left; intros m' mIn; inversion mIn; subst.
          generalize (Inc1_0 _ H1); intros.
          inversion H.
        * left; intros m' mIn; inversion mIn; subst.
          generalize (Inc2_0 _ H3); intros.
          inversion H.
        * right; intros m' mIn; inversion mIn; subst.
          econstructor.
          -- apply Inc1_1; eassumption.
          -- apply Inc2_1; eassumption.
          -- constructor.
      + Admitted.

  Lemma common_subpattern' : forall e f1 f2,
    ~ e ⊑ 𝟘 ->
    f1 ⊑ e ->
    f2 ⊑ e ->
    exists e', e' ⊑ f1 /\ e' ⊑ f2.
  Proof.
    induction e; induction f1; intros * Contra Inc1 Inc2;
    try match goal with
    | H: ~ 𝟘 ⊑ 𝟘 |- _ => exfalso; apply H; intros ? mIn; inversion mIn
    end.
    - exists 𝟘; split; try apply MPInclusion_refl; apply MPInclusion_zero.
    - exists f2; split; eauto using MPInclusion_refl, MPInclusion_trans.
    - assert (⟨ m ⟩ ∈ « m ») by constructor.
      generalize (Inc1 ⟨ m ⟩ H); intros C; inversion C.
    - Search (_ ⊑ 𝟙).
  Admitted.

  Lemma common_supertype'' : forall e f1 f2,
    ~ e ⊑ 𝟘 ->
    e ⊑ f1 ->
    e ⊑ f2 ->
    f1 ⊑ f2 \/ f2 ⊑ f1.
  Proof.
    induction e; intros * Contra Inc1 Inc2.
    - exfalso; now apply Contra.
    - assert (f1 ⊑ f1 ⊙ f1). admit.
  Admitted.



  Lemma common_supertype : forall T T1 T2,
    RuntimeSubtype T T1 ->
    RuntimeSubtype T T2 ->
    RuntimeSubtype T1 T2 \/ RuntimeSubtype T2 T1.
  Proof.
    intros * Sub1 Sub2.
    revert T2 Sub2.
    induction Sub1; intros.
    - inversion Sub2; subst; now left.
    - inversion Sub2; subst.
      left. constructor.
      admit.
    - inversion Sub2; subst.
      admit.
  Admitted.

  Lemma common_supertype' : forall T T1 T2,
    RuntimeSubtype T T1 ->
    RuntimeSubtype T T2 ->
    exists T', RuntimeSubtype T1 T' /\ RuntimeSubtype T2 T'.
  Proof.
    intros * Sub1 Sub2.
    inversion Sub1; subst; inversion Sub2; subst.
    - exists (TTBase c); split; apply RuntimeSubtype_refl.
    - generalize (common_superpattern _ _ _ H H1).
      intros [Inc1 Inc2].
      exists (TTMailbox (? f ⊕ f0)); split; now constructor.
    - eexists; split.
      + constructor. admit.
      + constructor. admit.
  Admitted.

  Lemma WellTypedConfig_exchange : forall prog x env T c,
    WellTypedConfig prog (raw_insert x T (raw_insert x T env)) c ->
    WellTypedConfig prog (raw_insert x T (raw_insert x T env)) (exchange_conf x c).
  Proof.
    intros *.
    revert x env T.
    induction c; intros * WT.
    - apply WellTypedConfig_ConfConf_inv in WT.
      destruct WT as [env' [T2 [env1 [env2 [Comb [WT_t [WT_s Sub]]]]]]].
      generalize (asvaefe _ _ _ _ Sub).
      intros [T1 [T3 [env2' ->]]].
      Search ((raw_insert _ _ _) ≤ₑ (raw_insert _ _ _)).
      destruct T, T1, T3.
      + assert (RuntimeSubtype t0 t1) by admit.
        assert (RuntimeSubtype t0 t2) by admit.
        assert (newEnv1 : exists env1', env1 = (insert x (returnType t1) (insert x (returnType t2) env1'))) by admit.
        destruct newEnv1 as [env1' ->].
        assert (newEnv2 : exists env2', env2 = (raw_insert x None (raw_insert x None env2'))) by admit.
        destruct newEnv2 as [env2'' ->].
        eapply SUBS.
        eassumption.
        econstructor.
        * eassumption.
        * 
    - admit.
    - admit.
    - apply WellTypedConfig_ConfRestr_inv'' in WT.
      simpl; constructor.
      assert (Eq : Some (TTMailbox (? 𝟙)) :: raw_insert x T (raw_insert x T env) = raw_insert (S x) T (raw_insert (S x) T (Some (TTMailbox (? 𝟙)) :: env)))
      by (repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero).
      rewrite Eq; eapply IHc; now rewrite <- Eq.

    intros * WT.
    remember (raw_insert x T (raw_insert x T env)) as E.
    revert x T env HeqE.
    induction WT; intros; inversion HeqE; subst.
    - simpl.
      constructor.
      assert (Eq : Some (TTMailbox (? 𝟙)) :: raw_insert x T (raw_insert x T env0) =
              raw_insert (S x) T (raw_insert (S x) T (Some (TTMailbox (? 𝟙)) :: env0)))
      by (repeat rewrite raw_insert_successor; now repeat rewrite lookup_zero).
      eapply IHWT; eassumption.
    - simpl.
      clear H0.
      admit.
    - simpl. admit.
    - simpl. admit.
    - 

    intros until x.
    induction x.
    - intros * WT.
      repeat rewrite raw_insert_zero in *.
      remember (T :: T :: env) as E.
      revert env HeqE.
      induction c; intros; inversion HeqE; subst.
      + simpl.
        apply WellTypedConfig_ConfConf_inv in WT.
        destruct WT as [env' [T2 [env1 [env2 [Comb [WT_t [WT_s Sub]]]]]]].
        econstructor.
        * admit.
        * admit.
        * admit.
      + simpl.
        admit. (* Need inversion lemma for message composition *)
      + simpl.
        admit. (* Need inversion lemma for parallel composition *)
      +




  Lemma Nu_exchange : forall prog env c,
    WellTypedConfig prog env (ConfRestr (ConfRestr c)) ->
    WellTypedConfig prog env (ConfRestr (ConfRestr (exchange_conf 0 c))).
  Proof.
    intros until c.
    revert env.
    induction c; intros * WT.
    - simpl.
      apply WellTypedConfig_ConfRestr_inv'' in WT.
      apply WellTypedConfig_ConfRestr_inv'' in WT.
      apply WellTypedConfig_ConfConf_inv in WT.
      destruct WT as [env3 [T [env3_1 [env3_2 [Comb [WT_t [WT_s Sub3]]]]]]].
      repeat constructor.
      eapply SUBS.
      + apply Sub3.
      + econstructor.
        * eassumption.
        * admit.
        * admit.
    - simpl. admit.
    - simpl.
      repeat apply WellTypedConfig_ConfRestr_inv'' in WT.
      admit. (* Need inversion lemma for parallel composition *)
    - apply WellTypedConfig_ConfRestr_inv'' in WT.
      generalize (IHc _ WT).
      intros WT'.
      assert (forall i c, exchange_conf i (exchange_conf i c) = c). admit.
      simpl.
      repeat apply WellTypedConfig_ConfRestr_inv'' in WT'.
      simpl.
      repeat constructor.
      generalize (H 0 c).
      admit. (* Need more general induction hypothesis *)
  Admitted.

  Lemma preservation_equiv : forall prog env r c d,
    WellTypedConfig prog env c ->
    StructEq c r d ->
    WellTypedConfig prog env d.
  Proof.
    intros * WT Struct.
    induction Struct.
    - destruct H.
      + now apply Par_comm.
      + now apply Par_assoc.
      + now apply Nu_exchange.
      +


  (*Lemma preservation_equiv : forall prog env c d,*)
  (*  WellTypedConfig prog env c ->*)
  (*  StructCongr c d ->*)
  (*  WellTypedConfig prog env d.*)
  (*Proof.*)
  (*  intros * WTc Congr.*)
  (*  revert env WTc.*)
  (*  induction Congr; intros.*)
  (*  - remember (ConfParallel c d) as C.*)
  (*    revert c d HeqC.*)
  (*    induction WTc; intros; inversion HeqC; subst.*)
  (*    + eapply PAR; try eassumption.*)
  (*      now apply RuntimeEnvironmentCombination_comm.*)
  (*    + eapply SUBS; try eassumption.*)
  (*      now apply IHWTc.*)
  (*  - remember (ConfParallel c (ConfParallel d e)) as C.*)
  (*    revert c d e HeqC.*)
  (*    induction WTc; intros; inversion HeqC; subst.*)
  (*    + remember (ConfParallel d0 e) as E'.*)
  (*      revert env d0 e HeqE' H.*)
  (*      clear IHWTc1 IHWTc2.*)
  (*      induction WTc2; intros; inversion HeqE'; subst.*)
  (*      * generalize (RuntimeEnvironmentCombination_assoc _ _ _ _ _ H0 H).*)
  (*        intros [env' [Comb1 Comb2]].*)
  (*        eapply PAR; try eapply PAR; eassumption.*)
  (*      * generalize (RuntimeEnvironmentCombination_Subtype_right _ _ env' _ H0 H).*)
  (*        intros [env'' [Comb' Sub']].*)
  (*        eapply SUBS; try eassumption.*)
  (*        apply IHWTc2; auto.*)
  (*    + eapply SUBS; try eassumption.*)
  (*      now apply IHWTc.*)
  (*  - remember (ConfRestr (ConfRestr c)) as C.*)
  (*    revert c HeqC.*)
  (*    induction WTc; intros; inversion HeqC; subst.*)
  (*    + do 2 apply NU.*)
  (*      replace (Some (TTMailbox (? 𝟙)) :: Some (TTMailbox (? 𝟙)) :: env) with (insert 0 (TTMailbox (? 𝟙)) (insert 0 (TTMailbox (? 𝟙)) env)) by now repeat rewrite raw_insert_zero.*)
  (*      apply WellTypedConfig_exchange.*)
  (*      repeat rewrite raw_insert_zero.*)
  (*      clear IHWTc HeqC.*)
  (*      remember (ConfRestr c0) as C'.*)
  (*      revert c0 HeqC'.*)
  (*      induction WTc; intros; inversion HeqC'; subst.*)
  (*      * easy.*)
  (*      * eapply SUBS with (env' := Some (TTMailbox (? 𝟙)) :: env').*)
  (*        -- constructor.*)
  (*           apply RuntimeSubtype_refl.*)
  (*           assumption.*)
  (*        -- now apply IHWTc.*)
  (*    + eapply SUBS; try eassumption.*)
  (*      now apply IHWTc.*)
  (*  - admit.*)
  (*  - assumption.*)
  (*  -*)
  (*Admitted.*)

  Ltac destruct_and H :=
    try lazymatch type of H with
    | True => clear H
    | exists _, _ =>
        let H1 := fresh in
        let H2 := fresh in
        destruct H as [H1 H2];
        destruct_and H2
    | _ /\ _ =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [ H1 H2 ];
      destruct_and H1; destruct_and H2
    end.

  Lemma ConfConf_TLet_inv : forall prog env t1 t2 stack,
    WellTypedConfig prog env (ConfConf (TLet t1 t2) stack) ->
    exists env' env1 env2 T env4 T' env3,
      RuntimeEnvironmentSubtype env env' /\
      WellTypedConfig prog env' (ConfConf (TLet t1 t2) stack) /\
      env1 ▷ₑ env2 ~= map_maybe returnType env' /\
      WellTypedTerm prog env1 (TLet t1 t2) T /\
      WellTypedStack prog env2 T stack /\
      WellTypedTerm prog (insert 0 ⌊ T' ⌋ env4) t2 T /\
      env3 ▷ₑ env4 ~= env1.
  Proof.
    intros * WT.
    remember (ConfConf (TLet t1 t2) stack) as C.
    revert t1 t2 stack HeqC.
    induction WT; intros; inversion HeqC; subst.
    - generalize (TLet_inv _ _ _ _ _ H0).
      intros [env' [T' [T1' [env1' [env2' [? [? [? [? ?]]]]]]]]].
      (*assert (SecondEnv env1). admit. (* This should hold *)*)
      (*assert (SecondEnv env'). admit. (* This should hold *)*)
      (*assert (SecondEnv env1'). admit. (* This should hold *)*)
      (*assert (SecondEnv env2'). admit. (* This should hold *)*)
      exists env, env1, env2, T, env2', T1', env1'; repeat split.
      + apply RuntimeEnvironmentSubtype_refl.
      + econstructor; eassumption.
      + assumption.
      + assumption.
      + assumption.
      + eapply SUB; eauto with environment.
      + admit.
    - generalize (IHWT _ _ _ eq_refl).
      intros E'.
      destruct_and E'.
      repeat eexists;
      try eapply EnvSubtypeTrans; eassumption.
  Admitted.

  Lemma TypeCombination_Sub : forall j j' k t,
    RuntimeSubtype (TTMailbox (? j)) (TTMailbox j') ->
    TTMailbox (? j) ⊞ TTMailbox k ~= TTMailbox t ->
    exists k' t',
      RuntimeSubtype (TTMailbox k) (TTMailbox k') /\
      RuntimeSubtype (TTMailbox t) (TTMailbox t') /\
      TTMailbox j' ⊞ TTMailbox k' ~= TTMailbox t'.
  Proof.
    intros * Sub Comb.
    remember (? j) as J.
    revert j' HeqJ Sub.
    induction Comb; intros; inversion HeqJ; subst; inversion Sub; subst.
    - exists (! f), (! f0 ⊙ f); split; constructor;
      try reflexivity.
      + constructor.
        intros m MIn.
        inversion MIn; subst.
        econstructor; eauto.
      + constructor.
    (*- exists (? f); split.*)
    (*  + apply RuntimeSubtype_refl.*)
    (*  + econstructor.*)
    (*    * constructor.*)
    (*      Print PatternEq.*)
        Admitted.

  Lemma MPInclusion_Comp : forall e1 e2 f,
    e1 ⊙ e2 ⊑ f ->
    exists e1' e2', f ≈ e1' ⊙ e2'.
  Proof.
    intros * Inc.
    destruct f.
    - admit.
    - exists 𝟙, 𝟙.
      now rewrite MPComp_unit.
    - 
      Search (_ ⊙ _).
      unfold MPInclusion in *.
      Admitted.

  Lemma TypeCombination_Sub_OutIn : forall e1 e2 f,
    e1 ⊙ e2 ⊑ f ->
    TTMailbox (? e1 ⊙ e2) ⊞ TTMailbox (! e1) ~= TTMailbox (? e2) ->
    exists e1' e2',
      e1' ⊑ e1 /\
      e2 ⊑ e2' /\
      (*RuntimeSubtype (TTMailbox k) (TTMailbox k') /\*)
      (*RuntimeSubtype (TTMailbox t) (TTMailbox t') /\*)
      TTMailbox (? f) ⊞ TTMailbox (! e1') ~= TTMailbox (? e2').
  Proof.
    intros * Inc Comb.
    generalize (MPInclusion_Comp _ _ _ Inc).
    intros [e1' [e2' [Eq1 Eq2]]].
    generalize (MPInclusion_trans _ _ _ Inc Eq1).
    intros Sub'.
    exists e1, e2'.
      Admitted.

  Lemma UsageCombination_Sub : forall j j' k t,
    j ≤ j' ->
    j ▷ k ~= t ->
    exists k' t',
      k ≤ k' /\
      t ≤ t' /\
      j' ▷ k' ~= t'.
  Proof.
    intros * Sub Comb.
    induction Comb; inversion Sub; subst.
    - repeat exists (TUBase c); repeat constructor.
    - inversion H0; subst.
      + rename e0 into e1.
        rename f0 into e2.
        inversion H; subst.
        * inversion H5; subst.
          generalize (TypeCombination_Sub_OutIn e1 e2 f H3 H0).
          intros [e1' [e2' [Sub1 [Sub2 Comb']]]].
          exists (! e1' ^^ ◦), (? e2' ^^ ◦); repeat constructor;
          assumption.
        * inversion H5; subst.
          generalize (TypeCombination_Sub_OutIn e1 e2 f H3 H0).
          intros [e1' [e2' [Sub1 [Sub2 Comb']]]].
          exists (! e1' ^^ ◦), (? e2' ^^ ◦); repeat constructor;
          assumption.
      + admit.
   Admitted.

  (*Lemma WellTypedStack_sub : forall p env env' T T' stack,*)
  (*  env ≤ₑ env' ->*)
  (*  T' ≤ T ->*)
  (*  WellTypedStack p env T stack ->*)
  (*  WellTypedStack p env' T' stack.*)
  (*Proof.*)
  (*  intros * EnvSub Sub WT.*)
  (*  revert env' T' Sub EnvSub.*)
  (*  induction WT; intros.*)
  (*  - constructor. eapply EmptyEnv_SubEnv_EmptyEnv; eassumption.*)
  (*  - econstructor.*)
  (*    Search (?env1 ▷ₑ ?env2 ~= ?env').*)
  (*    + Search (insert _ _ _).*)

  Lemma EnvironmentSubtype_insert : forall x env T T',
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

  Lemma WellTypedTerm_insert_Sub : forall x prog env T1 T1' T2 t,
    T1' ≤ T1 ->
    WellTypedTerm prog (insert x T1 env) t T2 ->
    WellTypedTerm prog (insert x T1' env) t T2.
  Proof.
    intros * Sub WT.
    eapply SUB with (env2 := insert x T1 env).
    - now apply EnvironmentSubtype_insert.
    - apply Subtype_refl.
    - assumption.
  Qed.

  Lemma WellTypedStack_sub : forall p env T T' stack,
    T' ≤ T ->
    WellTypedStack p env T stack ->
    WellTypedStack p env T' stack.
  Proof.
    intros * Sub WT.
    revert T' Sub.
    induction WT; intros.
    - now constructor.
    - econstructor.
      + eapply WellTypedTerm_insert_Sub; eassumption.
      + assumption.
      + eassumption.
      + assumption.
  Qed.

  Lemma WellTypedStack_raw_insert_None : forall p env T stack,
    WellTypedStack p env T stack ->
    WellTypedStack p (None :: env) T (lift_Stack stack).
  Proof.
    intros * WT.
    induction WT.
    - simpl; now repeat constructor.
    - eapply CONS with (env1 := None :: env1); try eassumption.
      + apply WellTypedTerm_raw_insert_None with (x := 0) in H.
        rewrite raw_insert_zero in H.
        now rewrite raw_insert_successor; rewrite lookup_zero; simpl.
      + now constructor.
  Qed.

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
    - remember (ConfConf (TLet t1 t2) stack) as C.
      revert t1 t2 stack HeqC.
      induction WT; intros; inversion HeqC; subst.
      + apply TLet_inv in H0.
        destruct H0 as [env' [TT [T1' [env3 [env4 [? [? [? [? ?]]]]]]]]].
        eapply THREAD.
        * admit.
        * eassumption.
        * admit.
      + eapply SUBS; try eassumption.
        apply IHWT.
        admit. (* Need lemma *)
        reflexivity.
    - remember (ConfConf (TValue v) ((x, t) :: stack)) as C.
      revert v t stack HeqC.
      induction WT; intros; inversion HeqC; subst.
      + inversion H1; subst.
        generalize (WellTypedEnvSub _ _ _ _ H0).
        intros [Pi1 [Pi2 [Pi3 [T' [Split [Sub [WT' [Cruftless [StrSub SubEnv]]]]]]]]].
        generalize (Subtype_Returnable).
        admit.
      + eapply SUBS; try eassumption.
        apply IHWT.
        admit. (* Need lemma *)
        reflexivity.
    - remember (ConfConf (TApp definition v) stack) as C.
      revert v stack HeqC.
      induction WT; intros; inversion HeqC; subst.
      + inversion H1; subst.
        * inversion WTP; subst.
          generalize (H3 definition).
          intros WTD; inversion WTD; subst.
          replace [Some argumentType1] with (insert 0 argumentType1 []) in H7 by apply raw_insert_zero.
          eapply THREAD with (T := T).
          -- eassumption.
          -- generalize (subst_lemma prog (create_EmptyEnv env1) env1 env1 argumentType1 argumentType0 T body v 0).
             admit.
          -- assumption.
        * admit.
      + eapply SUBS; try eassumption.
        apply IHWT.
        admit. (* Need lemma *)
        reflexivity.
    - remember (ConfConf TNew stack) as C.
      revert HeqC.
      induction WT; intros; inversion HeqC; subst.
      + clear HeqC.
        remember (TNew) as t.
        revert env2 H1 H Heqt.
        generalize dependent env.
        induction H0; intros; inversion Heqt; subst.
        * constructor.
          eapply THREAD with (env1 := Some (? 𝟙 ^^ •) :: env) (env2 := None :: env2) (T := (? 𝟙 ^^ •)).
          -- now constructor.
          -- rewrite <- raw_insert_zero.
             now constructor.
          -- now apply WellTypedStack_raw_insert_None in H1.
        * Search (TNew).
          assert (? 𝟙 ^^ • ≤ T1). admit.
          assert (env2 ≤ₑ create_EmptyEnv env2). admit.
          constructor.
          eapply THREAD with (env1 := Some (? 𝟙 ^^ •) :: env1) (env2 := None :: env0) (T := (? 𝟙 ^^ •)).
          -- now constructor.
          -- eapply SUB with (env2 := Some (? 𝟙 ^^ •) :: create_EmptyEnv env2).
             ++ constructor.
                apply Subtype_refl.
                eauto using EnvironmentSubtype_trans with environment.
             ++ apply Subtype_refl.
             ++ rewrite <- raw_insert_zero.
                constructor. apply create_EmptyEnv_EmptyEnv.
          -- admit.
      + eapply SUBS; try eassumption.
        apply IHWT.
        admit. (* Need lemma *)
        reflexivity.
    - admit.
    - admit.
    - admit.
    - admit.
    - remember (ConfRestr c) as C.
      revert HeqC.
      induction WT; intros; inversion HeqC; subst.
      + constructor.
        apply IHStep; try assumption.
        admit. (* Need lemma *)
      + apply SUBS with (env' := env'); try assumption.
        apply IHWT.
        admit. (* Need lemma *)
        reflexivity.
    - remember (ConfParallel c d) as C.
      revert HeqC.
      induction WT; intros; inversion HeqC; subst.
      + econstructor.
        * apply IHStep.
          -- admit. (* Need lemma *)
          -- eassumption.
        * eassumption.
        * assumption.
      + apply SUBS with (env' := env'); try eassumption.
        apply IHWT.
        admit. (* Need lemma *)
        reflexivity.
    - admit.
  Admitted.

  (** Lemma D.25 Progress (Thread Reduction) *)
  Lemma thread_reduction : forall prog env t stack,
    WellTypedConfig prog env (ConfConf t stack) ->
    (exists v, t = TValue v /\ stack = []) \/
    (exists t' stack', Step prog (ConfConf t stack) (ConfConf t' stack')) \/
    (t = TNew \/ (exists t', t = TSpawn t') \/ (exists v1 m v2, t = TSend v1 m v2) \/ (exists v e gs, t = TGuard v e gs)).
  Proof.
    intros * WT.
    remember (ConfConf t stack) as C.
    revert t stack HeqC.
    induction WT; intros; inversion HeqC; subst.
    - clear H HeqC.
      induction H0;
      try (repeat (right || left; eauto); fail).
      + destruct stack0.
        * left; eauto.
        * right; left.
          destruct f.
          exists (subst (ValueVar x) v t).
          exists stack0.
          apply stepReturn.
      + destruct stack0.
        * left; eauto.
        * right; left.
          destruct f.
          exists (subst (ValueBool true) v t).
          exists stack0.
          apply stepReturn.
      + destruct stack0.
        * left; eauto.
        * right; left.
          destruct f.
          exists (subst (ValueBool false) v t).
          exists stack0.
          apply stepReturn.
      + destruct stack0.
        * left; eauto.
        * right; left.
          destruct f.
          exists (subst ValueUnit v t).
          exists stack0.
          apply stepReturn.
      + right; left.
        eexists; eexists.
        eapply stepApp; eassumption.
      + right; left.
        eexists; eexists.
        eapply stepLet.
      + apply IHWellTypedTerm.
        eapply WellTypedStack_sub; eassumption.
    - now apply IHWT.
  Qed.

End runtime_props.
