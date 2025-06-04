(** * Substitution *)

From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.
From MailboxTypes Require Import TypingRules.
From MailboxTypes Require Import Dblib.DeBruijn.
From MailboxTypes Require Import Dblib.DblibTactics.

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
    | TGuard v e guards => TGuard (traverse_Value f l v) e (map (traverse_Guard f l) guards)
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
    map (traverse_Guard (fun l x : nat => ValueVar (f l x)) n) l1 =
    map (traverse_Guard (fun l x : nat => ValueVar (f l x)) n) l2 ->
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
    - symmetry in mTrav; now apply map_eq_nil in mTrav.
    - inversion H; subst.
      symmetry in mTrav; apply map_eq_cons in mTrav.
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


  Lemma EmptyEnv_app_cons : forall env1 env2 T, ~ EmptyEnv (env1 ++ Some T :: env2).
  Proof.
    induction env1; intros.
    - intros E; inversion E; subst; discriminate.
    - destruct a; intros E; inversion E; subst.
      + discriminate.
      + now apply IHenv1 in H2.
  Qed.

  Lemma SingletonEnv_app_cons : forall env1 env2 T,
    SingletonEnv (env1 ++ Some T :: env2) ->
    EmptyEnv env1 /\ EmptyEnv env2.
  Proof.
    induction env1; intros.
    - repeat constructor; assumption.
    - simpl in *. destruct a.
      + now apply EmptyEnv_app_cons in H.
      + apply IHenv1 in H; destruct H.
        repeat constructor; assumption.
  Qed.

  Lemma lookup_app_cons_weak : forall v env1 env2 T1 T2,
    lookup v (None :: env1 ++ Some T1 :: env2) = Some T2 ->
    lookup (v - 1) (env1 ++ Some T1 :: env2) = Some T2.
  Proof.
    induction v; intros; simpl in *.
    - discriminate.
    - now rewrite PeanoNat.Nat.sub_0_r.
  Qed.

  Lemma SingletonEnv_lookup_Some : forall env1 env2 T1 T2 v,
    lookup v (env1 ++ Some T1 :: env2) = Some T2 ->
    SingletonEnv (env1 ++ Some T1 :: env2) ->
    T1 = T2.
  Proof.
    induction env1; intros.
    - simpl in *.
      destruct v.
      + now inversion H.
      + simpl in *.
        apply EmptyEnv_lookup with (x := v) in H0.
        rewrite H in H0; discriminate.
    - simpl in *.
      destruct a; simpl in *.
      + now apply EmptyEnv_app_cons in H0.
      + eapply IHenv1 with (v := v - 1) (env2 := env2).
        * now apply lookup_app_cons_weak.
        * assumption.
  Qed.

  From MailboxTypes Require Import Dblib.Environments.

  Inductive EnvironmentSubtype' : Env -> Env -> Prop :=
    | EnvSubtypeUn : forall env1 env2 x T,
        lookup x env2 = None ->
        Unrestricted T ->
        EnvironmentSubtype' env1 env2 ->
        EnvironmentSubtype' (insert x T env1) env2
    | EnvSubtypeSub : forall env1 env2 x T1 T2,
        Subtype T1 T2 ->
        EnvironmentSubtype' env1 env2 ->
        EnvironmentSubtype' (insert x T1 env1) (insert x T2 env2)
    | EnvSubtypeTrans : forall env1 env2 env3,
        EnvironmentSubtype' env1 env2 ->
        EnvironmentSubtype' env2 env3 ->
        EnvironmentSubtype' env1 env3
    | EnvSubtypeRefl : forall env, EnvironmentSubtype' env env.

  Lemma EnvSubtypeUn'_inv_EmptyEnv :
    forall x env T', Unrestricted T' -> EnvironmentSubtype' (insert x T' env) env.
  Proof.
    intros.
    constructor.
  Admitted.

  Lemma weakening : forall p env t T,
    WellTypedTerm p env t T ->
    forall x T' env',
    Unrestricted T' ->
    insert x T' env = env' ->
    WellTypedTerm p env' (shift x t) T.
  Proof.
  Admitted.

  Lemma subst_lemma_TValue : forall p env1 env2 env A A' B v1 v2 x,
    WellTypedTerm p (insert x A env1) (TValue v1) B ->
    WellTypedTerm p env2 (TValue v2) A' ->
    A' ≤ A ->
    env1 +ₑ env2 ~= env ->
    WellTypedTerm p env (subst v2 x (TValue v1)) B.
  Proof.
    intros * WT1.
    remember (insert x A env1) as E.
    remember (TValue v1) as V.
    revert x v1 v2 A A' env1 HeqE HeqV.
    induction WT1; intros * ? ? WT2 Sub Dis; try discriminate.
    - subst. simpl_subst_goal. simpl.
      unfold subst_idx.
      dblib_by_cases.
      + admit.
      + rewrite lift_zero. admit. (* this works with a few lemmas *)
      + simpl. admit.
    - subst. admit. (* EmptyEnv (insert x A env1) -> False *)
    - subst. admit. (* EmptyEnv (insert x A env1) -> False *)
    - subst. admit. (* EmptyEnv (insert x A env1) -> False *)
    - subst. eapply SUB.
      + apply EnvironmentSubtype_refl.
      + eassumption.
      + eapply IHWT1.


  Lemma subst_lemma_TValue : forall p env1_1 env1_2 env2 env A A' B v1 v2,
    WellTypedTerm p (env1_1 ++ Some A :: env1_2) (TValue v1) B ->
    WellTypedTerm p env2 (TValue v2) A' ->
    A' ≤ A ->
    (env1_1 ++ None :: env1_2) +ₑ env2 ~= env ->
    WellTypedTerm p env (subst v2 (length env1_1) (TValue v1)) B.
  Proof.
    intros * WT1.
    remember (TValue v1) as V.
    remember (env1_1 ++ Some A :: env1_2) as E.
    revert env1_1 env1_2 v1 A HeqV HeqE v2 A' env2 env.
    induction WT1; intros * Eq1 Eq2 * WT2 Sub Dis; try discriminate.
    - injection Eq1; intros; subst.
      simpl_subst_goal. simpl.
      rewrite lift_zero.
      Search (subst_idx).
      assert (Greater : v > (length env1_1)). admit.
      simpl_subst_goal.
      (*rewrite subst_idx_miss_2.*)
      (*+ simpl.*)
      (*  generalize (SingletonEnv_lookup_Some _ _ _ _ _ H0 H).*)
      (*  intros ->.*)
      (*  constructor.*)
      (**)
      admit.
    - subst; now apply EmptyEnv_app_cons in H.
    - subst; now apply EmptyEnv_app_cons in H.
    - subst; now apply EmptyEnv_app_cons in H.
    - subst. induction env1_1.
      + simpl in *.
        simpl_subst_goal; simpl.
        Search (lift _ 0 _).
      
      injection Eq1; intros ->; subst.

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
