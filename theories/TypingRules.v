(** * Typing rules of the Pat programming language *)

From MailboxTypes Require Export Types.
From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Message.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.

From Stdlib Require Import Lists.List.
Import ListNotations.

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
  | SPAWN : forall env t,
      WellTypedTerm prog env t (TUBase BTUnit) ->
      WellTypedTerm prog ⌈ env ⌉ₑ (TSpawn t) (TUBase BTUnit)
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
    WellTypedTerm prog nil (initialTerm prog) (TUBase BTUnit) -> WellTypedProgram prog.

  Scheme WellTypedTerm_ind3 := Minimality for WellTypedTerm Sort Prop
    with WellTypedGuards_ind3 := Minimality for WellTypedGuards Sort Prop
    with WellTypedGuard_ind3 := Minimality for WellTypedGuard Sort Prop.

End typing_rules_def.

Hint Constructors WellTypedTerm : environment.

(*
Section well_typed_ind'.

  Generalizable All Variables.
  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

  Variables (p : Prog).
  Variable P : Env -> Term -> TUsage -> Prop.
  Variable PGs : Env -> list Guard -> TUsage -> MPattern -> Prop.
  Variable PG : Env -> Guard -> TUsage -> MPattern -> Prop.

  Hypothesis VAR_case : forall v env T,
    SingletonEnv env ->
    lookup v env = Some T ->
    P env (TValue (ValueVar (Var v))) T.
  Hypothesis TRUE_case : forall env,
    EmptyEnv env -> P env (TValue (ValueBool true)) (TUBase BTBool).
  Hypothesis FALSE_case : forall env,
    EmptyEnv env -> P env (TValue (ValueBool false)) (TUBase BTBool).
  Hypothesis UNIT_case : forall env,
    EmptyEnv env -> P env (TValue (ValueUnit)) (TUBase BTUnit).
  Hypothesis APP_case : forall env envList vList definition bodyType argumentTypes term,
    definitions p definition = FunDef definition argumentTypes bodyType term ->
    [envList]+ₑ ~= env ->
    Forall3 P envList (map TValue vList) argumentTypes ->
    P env (TApp definition vList) bodyType.
  Hypothesis LET_case : forall (env env1 env2 : Env) (T1 : TType) (T2 : TUsage) (t1 t2 : Term),
    env1 ▷ₑ env2 ~= env ->
    P env1 t1 ⌊ T1 ⌋ ->
    P (Some ⌊ T1 ⌋ :: env2) t2 T2 ->
    P env (TLet t1 t2) T2.
  Hypothesis SPAWN_case : forall env t,
      P env t (TUBase BTUnit) ->
      P ⌈ env ⌉ₑ (TSpawn t) (TUBase BTUnit).
  Hypothesis NEW_case : forall env,
      EmptyEnv env ->
      P env TNew (? 𝟙 ^^ •).
  Hypothesis SEND_case : forall env env' envList tList vList m v,
      P env' (TValue v) (! « m » ^^ ◦) ->
      signature p m = tList ->
      [ (env' :: envList) ]+ₑ ~= env ->
      Forall3 P envList (map TValue vList) (map secondType tList) ->
      P env (TSend v m vList) (TUBase BTUnit).
  Hypothesis GUARD_case : forall env env1 env2 guards v T e f,
      env1 +ₑ env2 ~= env ->
      P env1 (TValue v) (? f ^^ •) ->
      PGs env2 guards T f ->
      e ⊑ f ->
      f ⊧ f ->
      P env (TGuard v e guards) T.
  Hypothesis SUB_case : forall t env1 env2 T1 T2,
      env1 ≤ₑ env2 ->
      T1 ≤ T2 ->
      P env2 t T1 ->
      P env1 t T2.
  Hypothesis SINGLE_case : forall T e env g,
      PG env g T e ->
      PGs env (g :: nil) T e.
  Hypothesis SEQ_case : forall T e es env guards g,
      PG env g T e ->
      PGs env guards T es ->
      PGs env (g :: guards) T (e ⊕ es).
  Hypothesis FAIL_case : forall t env, PG env GFail t 𝟘.
  Hypothesis FREE_case : forall t env T,
      P env t T ->
      PG env (GFree t) T 𝟙.
  Hypothesis RECEIVE_case : forall t m env T tList e mailbox,
      signature p m = tList ->
      BaseTypes tList \/ BaseEnv env ->
      P ((toEnv (map secondType tList)) ++ [Some (? e ^^ •)] ++ env) t T ->
      PG env (GReceive m mailbox t) T (« m » ⊙ e).

  Definition WellTypedTerm_ind' : forall {env t T}, WellTypedTerm p env t T -> P env t T.
  Proof.
    refine(
      fix F {env t T} (WT : WellTypedTerm p env t T) : P env t T :=
        match WT in (WellTypedTerm _ env' t' T') return (P env' t' T') with
        | VAR _ v env T Single Lookup => VAR_case v env T Single Lookup
        | TRUE _ env Empty => TRUE_case env Empty
        | FALSE _ env Empty => FALSE_case env Empty
        | UNIT _ env Empty => UNIT_case env Empty
        | APP _ env envList vList def bT aT t L Dis F3 =>
            APP_case env envList vList def bT aT t L Dis
              ((fix F3_ind {envList2 vList2 aT2} (F3_WT : Forall3 _ envList2 vList2 aT2) {struct F3_WT} : Forall3 P envList2 vList2 aT2 :=
                 match F3_WT in (Forall3 _ envList' vList' aT') return (Forall3 P envList' vList' aT') with
                 | Forall3_nil _ => Forall3_nil _
                 | Forall3_cons _ t' T' WT' F3' => Forall3_cons _ t' T' (F WT') (F3_ind F3')
                 end
              ) envList (map TValue vList) aT F3)
        | LET _ env env1 env2 T1 T2 t1 t2 Dis WT1 WT2 =>
            LET_case env env1 env2 T1 T2 t1 t2 Dis (F WT1) (F WT2)
        | SPAWN _ env t WT => SPAWN_case env t (F WT)
        | NEW _ env Empty => NEW_case env Empty
        | SEND _ env env' envList tList vList m v WT s Dis F3 =>
            SEND_case env env' envList tList vList m v (F WT) s Dis
              ((fix F3_ind {envList2 vList2 tList2} (F3_WT : Forall3 _ envList2 vList2 tList2) {struct F3_WT} : Forall3 P envList2 vList2 tList2 :=
                 match F3_WT in (Forall3 _ envList' vList' tList') return (Forall3 P envList' vList' tList') with
                 | Forall3_nil _ => Forall3_nil _
                 | Forall3_cons _ t' T' WT' F3' => Forall3_cons _ t' T' (F WT') (F3_ind F3')
                 end
              ) envList (map TValue vList) (map secondType tList) F3)
        | GUARD _ env env1 env2 guards v T e f Dis WT WTGs Inc PNF =>
            GUARD_case env env1 env2 guards v T e f Dis (F WT) (FGs WTGs) Inc PNF
        | SUB _ t env1 env2 T1 T2 SubEnv Sub WT' => SUB_case _ _ _ _ _ SubEnv Sub (F WT')
        end
      with FGs {env gs T e} (WTGs : WellTypedGuards p env gs T e) : PGs env gs T e :=
        match WTGs in (WellTypedGuards _ env' gs' T' e') return (PGs env' gs' T' e') with
        | SINGLE _ _ _ _ _ WTG' => SINGLE_case _ _ _ _ (FG WTG')
        | SEQ _ _ _ _ _ _ _ WTG' WTGs' => SEQ_case _ _ _ _ _ _ (FG WTG') (FGs WTGs')
        end
      with FG {env g T e} (WTG : WellTypedGuard p env g T e) : PG env g T e :=
        match WTG in (WellTypedGuard _ env' g' T' e') return (PG env' g' T' e') with
        | FAIL _ env t => FAIL_case env t
        | FREE _ t env T WT' => FREE_case t env T (F WT')
        | RECEIVE _ _ _ _ _ _ _ _ s Base WT' => RECEIVE_case _ _ _ _ _ _ _ s Base (F WT')
        end
      for F
    ).
  Defined.

End well_typed_ind'.
*)

Section well_typed_def.

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

(* TODO: Move to environment file *)

(** The domain of an environment is equal to the free variables in a term *)
Definition EnvEqFV (env : Env) (m : Term) :=
  forall x, In x (FV m) <-> is_Some (lookup x env).

(** Definition D.3 of cruftless.
   An environment is cruftless for a term, if the term is well-typed under
   the environment and the domain of the environment is equal to the
   free variables in the term.
*)
Definition Cruftless {p : Prog} (env : Env) (m : Term) :=
  exists T, WellTypedTerm p env m T /\ EnvEqFV env m.


(*Lemma EnvironmentSubtype_nil : forall env, [] ≤ₑ env -> env = [].*)
(*Proof.*)
(*  intros * Sub.*)
(*  remember [] as E.*)
(*  induction Sub;*)
(*  try (symmetry in HeqE; now apply empty_eq_insert in HeqE).*)
(*  - rewrite IHSub2; now rewrite IHSub1.*)
(*  - reflexivity.*)
(*Qed.*)

(*Lemma WT_empty_Var : forall p v T, ~ WellTypedTerm p [] (TValue (ValueVar v)) T.*)
(*Proof.*)
(*  intros * WT.*)
(*  remember (TValue (ValueVar v)) as V.*)
(*  remember [] as E.*)
(*  induction WT; try (discriminate HeqV).*)
(*  + symmetry in HeqE; now apply empty_eq_insert in HeqE.*)
(*  + subst; apply IHWT; (reflexivity || now apply EnvironmentSubtype_nil).*)
(*Qed.*)

(*Lemma not_EmptyEnv_and_SingletonEnv : forall env,*)
(*  ~ (EmptyEnv env /\ SingletonEnv env).*)
(*Proof.*)
(*  induction env.*)
(*  - simpl. intuition.*)
(*  - simpl. destruct a.*)
(*    + intros [Empty1 _]. inversion Empty1; subst. discriminate.*)
(*    + assert (EmptyEnv (None :: env) <-> EmptyEnv env).*)
(*      {*)
(*        split.*)
(*        - intros H; now inversion H.*)
(*        - intros H; now constructor.*)
(*      }*)
(*      now rewrite H.*)
(*Qed.*)
(**)
(*Lemma WT_EmptyEnv_Var : forall p v T env,*)
(*  EmptyEnv env ->*)
(*  ~ WellTypedTerm p env (TValue (ValueVar v)) T.*)
(*Proof.*)
(*  intros * Empty WT.*)
(*  remember (TValue (ValueVar v)) as V.*)
(*  induction WT; try (discriminate HeqV).*)
(*  + induction env.*)
(*    * inversion H.*)
(*    * destruct a.*)
(*      -- inversion Empty; subst; discriminate.*)
(*      -- now apply not_EmptyEnv_and_SingletonEnv with (env := None :: env).*)
(*  + subst; apply IHWT.*)
(*    * now apply EmptyEnv_SubEnv_EmptyEnv with (env1 := env1).*)
(*    * reflexivity.*)
(*Qed.*)

(* TODO: Cleanup proof *)
(*Lemma EnvironmentSubtype_diff_Sub_Cruftless_TValue : forall p env1 env2 v,*)
(*  env1 ≤ₑ env2 ->*)
(*  @Cruftless p env2 (TValue v) ->*)
(*  @Cruftless p (EnvironmentSubtype_diff_Sub env1 env2) (TValue v).*)
(*Proof.*)
(*  intros * Sub [T [WT Eq]]; unfold Cruftless in *.*)
(*  destruct v.*)
(*  - destruct b.*)
(*    + unfold EnvEqFV in *.*)
(*      exists (TUBase BTBool); split.*)
(*      * constructor; apply EnvironmentSubtype_diff_Sub_Empty.*)
(*        now apply lookup_False_EmptyEnv.*)
(*      * simpl in *. apply lookup_False_EmptyEnv in Eq.*)
(*        generalize (EnvironmentSubtype_diff_Sub_Empty env1 env2 Eq).*)
(*        intros Empty x; apply EmptyEnv_lookup with (x := x) in Empty; now rewrite Empty.*)
(*    + unfold EnvEqFV in *.*)
(*      exists (TUBase BTBool); split.*)
(*      * constructor; apply EnvironmentSubtype_diff_Sub_Empty.*)
(*        now apply lookup_False_EmptyEnv.*)
(*      * simpl in *. apply lookup_False_EmptyEnv in Eq.*)
(*        generalize (EnvironmentSubtype_diff_Sub_Empty env1 env2 Eq).*)
(*        intros Empty x; apply EmptyEnv_lookup with (x := x) in Empty; now rewrite Empty.*)
(*  - exists (TUBase BTUnit); split.*)
(*    + constructor; apply EnvironmentSubtype_diff_Sub_Empty.*)
(*      now apply lookup_False_EmptyEnv.*)
(*    + simpl in *. apply lookup_False_EmptyEnv in Eq.*)
(*      generalize (EnvironmentSubtype_diff_Sub_Empty env1 env2 Eq).*)
(*      intros Empty x; apply EmptyEnv_lookup with (x := x) in Empty; now rewrite Empty.*)
(*  - unfold EnvEqFV in *. destruct v; simpl in *.*)
(*    specialize (lookup_False_n _ _ Eq); intros Lookup.*)
(*    destruct Lookup as [T' Lookup].*)
(*    generalize (EnvironmentSubtype_diff_Sub_lookup _ _ n T' Sub Lookup).*)
(*    intros [T'' Lookup'].*)
(*    exists T''; split; simpl in *.*)
(*    + constructor.*)
(*      * apply lookup_False_SingletonEnv in Eq.*)
(*        now apply EnvironmentSubtype_diff_Sub_Singleton.*)
(*      * assumption.*)
(*    + intros x.*)
(*      destruct (PeanoNat.Nat.eq_dec n x).*)
(*      * subst; intuition. now rewrite Lookup'.*)
(*      * eapply SingletonEnv_lookup_None with (y := x) in Lookup'.*)
(*        rewrite Lookup'; intuition.*)
(*        apply lookup_False_SingletonEnv in Eq.*)
(*        apply EnvironmentSubtype_diff_Sub_Singleton; assumption.*)
(*        assumption.*)
(*Qed.*)

(*Lemma xfdx : forall p env1 env2 t T,*)
(*  EnvEqFV env1 t ->*)
(*  env1 ≤ₑ env2 ->*)
(*  WellTypedTerm p env2 t T ->*)
(*  EnvEqFV env2 t.*)
(*Proof.*)
(*  intros until t.*)
(*  revert env1 env2.*)
(*  induction t; intros * Eq Sub WT.*)
(*  - destruct v; unfold EnvEqFV in *; simpl in *.*)
(*    + remember (TValue (ValueBool b)) as V.*)
(*      induction WT; try discriminate.*)
(*      * now apply lookup_False_EmptyEnv'.*)
(*      * now apply lookup_False_EmptyEnv'.*)
(*      * apply lookup_False_EmptyEnv'.*)
(*        apply lookup_False_EmptyEnv in Eq.*)
(*        now apply EmptyEnv_SubEnv_EmptyEnv with (env1 := env1).*)
(*    + inversion WT; subst.*)
(*      * now apply lookup_False_EmptyEnv'.*)
(*      * apply lookup_False_EmptyEnv'.*)
(*        apply lookup_False_EmptyEnv in Eq.*)
(*        now apply EmptyEnv_SubEnv_EmptyEnv with (env1 := env1).*)
(*    + inversion WT; subst.*)
(*      * simpl in *.*)
(*        apply lookup_False_SingletonEnv in Eq.*)
(*        intros.*)
(*        destruct (PeanoNat.Nat.eq_dec v x).*)
(*        -- subst. rewrite H2; simpl; intuition.*)
(*        -- generalize (SingletonEnv_lookup_None _ _ _ H0 H2 x n).*)
(*           intros ->; simpl; intuition.*)
(*      * admit.*)
(*  - unfold EnvEqFV in *; simpl in *; inversion WT; subst.*)
(*    + admit.*)
(*Admitted.*)

(*Lemma EnvironmentSubtype_diff_Sub_Cruftless_TLet : forall p env t1 t2,*)
(*  @Cruftless p env (TLet t1 t2) ->*)
(*  exists env1 env2 T, @Cruftless p env1 t1 /\ @Cruftless p (Some ⌊ T ⌋ :: env2) t2.*)
(*Proof.*)
(*  intros * Cruftl.*)
(*  unfold Cruftless in *; unfold EnvEqFV.*)
(*  destruct Cruftl as [T [WT Eq]].*)
(*  remember (TLet t1 t2) as L.*)
(*  induction WT; subst; try discriminate.*)
(*  - admit.*)
(*  - apply IHWT.*)
(*    + reflexivity.*)
(*    + eapply xfdx.*)
(*      apply Eq.*)
(*      assumption.*)
(*      apply WT.*)
(*Admitted.*)

(*Lemma ValueVar_Cruftless : forall {p} env v T,*)
(*  SingletonEnv env ->*)
(*  lookup v env = Some T ->*)
(*  @Cruftless p env (TValue (ValueVar v)).*)
(*Proof.*)
(*  intros * Singleton Lookup.*)
(*  unfold Cruftless.*)
(*  exists T.*)
(*  split.*)
(*  - now constructor.*)
(*  - intros x.*)
(*    simpl.*)
(*    intuition.*)
(*    + unfold is_Some. subst. now rewrite Lookup.*)
(*    + destruct (lookup x env) eqn:xLookup.*)
(*      * generalize (SingletonEnv_lookup_eq env v x T t Singleton Lookup xLookup).*)
(*        intuition.*)
(*      * intuition.*)
(*Qed.*)

(*Lemma stes : forall env T,*)
(*  (forall x, 0 = x \/ False <-> is_Some (lookup x (Some T :: env))) ->*)
(*  (forall x, False <-> is_Some (lookup x env)).*)
(*Proof.*)
(*  intros * Eq x.*)
(*  generalize (Eq (S x)).*)
(*  intros EqX.*)
(*  destruct x.*)
(*  - intuition. discriminate H0.*)
(*  - intuition. discriminate H0.*)
(*Qed.*)
(**)
(*Lemma stes' : forall env n T,*)
(*  (forall x, n = x \/ False <-> is_Some (lookup x (Some T :: env))) ->*)
(*  n = 0.*)
(*Proof.*)
(*  induction n; intros * Eq.*)
(*  - reflexivity.*)
(*  - generalize (Eq 0); simpl; intuition.*)
(*Qed.*)

(*Lemma canonical_form_BTBool : forall {p} env v,*)
(*  WellTypedTerm p env (TValue v) (TUBase BTBool) ->*)
(*  v = ValueBool false \/ v = ValueBool true \/ exists n, v = ValueVar n.*)
(*Proof.*)
(*  intros * WT.*)
(*  remember (TUBase BTBool) as T.*)
(*  destruct v.*)
(*  - destruct b; intuition.*)
(*  - remember (TValue ValueUnit) as V.*)
(*    induction WT; try (discriminate HeqV); try (discriminate HeqT).*)
(*    subst.*)
(*    apply Subtype_inversion_TUBase_right in H0.*)
(*    now apply IHWT.*)
(*  - remember (TValue (ValueVar v)) as V.*)
(*    induction WT; try (discriminate HeqT); try (discriminate HeqV).*)
(*    + repeat right. exists v0. now inversion HeqV.*)
(*    + subst.*)
(*      apply Subtype_inversion_TUBase_right in H0.*)
(*      now apply IHWT.*)
(*Qed.*)

(*Lemma canonical_form_BTUnit : forall {p} env v,*)
(*  WellTypedTerm p env (TValue v) (TUBase BTUnit) ->*)
(*  v = ValueUnit \/ exists n, v = ValueVar n.*)
(*Proof.*)
(*  intros * WT.*)
(*  remember (TUBase BTUnit) as T.*)
(*  remember (TValue v) as V.*)
(*  induction WT; try (discriminate HeqT); try (discriminate HeqV).*)
(*  + right; exists v0; now inversion HeqV.*)
(*  + left; now inversion HeqV.*)
(*  + subst; apply Subtype_inversion_TUBase_right in H0; now apply IHWT.*)
(*Qed.*)
(**)
(*Lemma test' : forall vList tList t,*)
(*  t :: tList = map TValue vList ->*)
(*  exists v vList', t = TValue v /\ tList = map TValue vList'.*)
(*Proof.*)
(*  induction vList; simpl; intros * Eq.*)
(*  - discriminate Eq.*)
(*  - inversion Eq.*)
(*    now exists a, vList.*)
(*Qed.*)

(*Lemma lookup_None : forall n env T,*)
(*  lookup n (None :: env) = Some T -> lookup (n-1) env = Some T.*)
(*Proof.*)
(*  intros n.*)
(*  induction env; simpl; intros * Eq.*)
(*  - induction n; simpl in *.*)
(*    + discriminate.*)
(*    + rewrite lookup_nil in Eq; discriminate.*)
(*  - induction n; simpl in *.*)
(*    + discriminate.*)
(*    + replace (n-0) with n. assumption.*)
(*      now destruct n.*)
(*Qed.*)

(*Lemma WellTypedEnvSub_TValueVar :*)
(*  forall {T p} env v,*)
(*  WellTypedTerm p env (TValue (ValueVar v)) T ->*)
(*  exists env1 env2 env3 T',*)
(*    env1,, env2 ~= env /\*)
(*    T' ≤ T /\*)
(*    WellTypedTerm p env3 (TValue (ValueVar v)) T' /\*)
(*    @Cruftless p env1 (TValue (ValueVar v)) /\*)
(*    env1 ≼ₑ env3 /\*)
(*    UnrestrictedEnv env2.*)
(*Proof.*)
(*  intros * WT.*)
(*  remember (TValue (ValueVar v)) as V.*)
(*  induction WT; try (subst; discriminate).*)
(*  - inversion HeqV. subst.*)
(*    exists env, (create_EmptyEnv env), env, T.*)
(*    repeat split.*)
(*    + apply EnvironmentSplit_create_EmptyEnv.*)
(*    + apply Subtype_refl.*)
(*    + now constructor.*)
(*    + now apply ValueVar_Cruftless with (T := T).*)
(*    + apply EnvironmentSubtypeStrict_refl.*)
(*    + admit. (*apply CruftEnv_EmptyEnv; apply create_EmptyEnv_EmptyEnv.*)*)
(*  - subst.*)
(*    generalize (IHWT eq_refl).*)
(*    intros [env1' [env2' [env3' [T' [Split [Sub [WT' [Cruftless' [SubStrict Cruft']]]]]]]]].*)
(*    clear IHWT.*)
(*    (*generalize (EnvironmentSubtype_diff_CruftEnv env1 env2 H). intros.*)*)
(*    (*exists env1', env2', env3', T'.*)*)
(*    (*repeat split.*)*)
(*    (*+ admit.*)*)
(*    (*+ eapply Subtype_trans. apply Sub. assumption.*)*)
(*    (*+ assumption.*)*)
(*    (*+ assumption.*)*)
(*    (*+ assumption.*)*)
(*    (*+ assumption.*)*)
(*Admitted.*)

(*Lemma WellTypedEnvSub_TValue :*)
(*  forall p env v T,*)
(*  WellTypedTerm p env (TValue v) T ->*)
(*  exists env1 env2 env3 T',*)
(*    env1,, env2 ~= env /\*)
(*    T' ≤ T /\*)
(*    WellTypedTerm p env3 (TValue v) T' /\*)
(*    @Cruftless p env1 (TValue v) /\*)
(*    env1 ≼ₑ env3 /\*)
(*    CruftEnv env2.*)
(*Proof.*)
(*  intros * WT.*)
(*  remember (TValue v) as V.*)
(*  induction WT; try discriminate.*)
(*  - admit.*)
(*  - admit.*)
(*  - admit.*)
(*  - admit.*)
(*  - subst.*)
(*    generalize (IHWT eq_refl).*)
(*    intros [env1' [env2' [env3' [T' [Split [Sub [WT' [Cruftless' [SubStrict Cruft']]]]]]]]].*)
(*    clear IHWT.*)
(*Admitted.*)
(**)

(** Lemma D.4 *)
(*Lemma WellTypedEnvSub :*)
(*  forall {T p} env m,*)
(*  WellTypedTerm p env m T ->*)
(*  exists env1 env2 env3 T',*)
(*    env1,, env2 ~= env /\*)
(*    T' ≤ T /\*)
(*    WellTypedTerm p env3 m T' /\*)
(*    @Cruftless p env1 m /\*)
(*    env1 ≼ₑ env3 /\*)
(*    CruftEnv env2.*)
(*Proof.*)
(*Admitted.*)

End well_typed_def.
