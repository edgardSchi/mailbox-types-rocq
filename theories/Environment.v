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
(*Definition Env := list (option TUsage).*)
Definition Env := env TUsage.

(** Lookup the type of an variable in an environment *)
(*Fixpoint lookup (n : nat) (env : Env) : option TUsage :=*)
(*  match n, env with*)
(*  | _, nil => None*)
(*  | 0, (None :: env') => None*)
(*  | 0, (Some T :: env') => Some T*)
(*  | S n', (_ :: env') => lookup n' env'*)
(*  end.*)

(** Convert a list of types to an environment. This reverses the list. *)
(*Definition toEnv (l : list TUsage) : Env :=*)
(*  map Some (rev l).*)

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
  (* TODO: Check if this is correct *)
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
  (* TODO: Check if this is correct *)
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

Section environment_test.

Context `{M : IMessage Message}.

(* This relation states that an environment can be split into two environments **)
Inductive EnvironmentSplit : Env -> Env -> Env -> Prop :=
  | EnvSplitNil : EnvironmentSplit nil nil nil
  | EnvSplitNone : forall env1 env2 env,
      EnvironmentSplit env1 env2 env ->
      EnvironmentSplit (None :: env1) (None :: env2) (None :: env)
  | EnvSplitLeft : forall env1 env2 env x,
      EnvironmentSplit env1 env2 env ->
      EnvironmentSplit (Some x :: env1) (None :: env2) (Some x :: env)
  | EnvSplitRight : forall env1 env2 env x,
      EnvironmentSplit env1 env2 env ->
      EnvironmentSplit (None :: env1) (Some x :: env2) (Some x :: env).

Inductive EnvironmentSplitN : list Env -> Env -> Prop :=
  | EnvSplit2 : forall env env1 env2,
      EnvironmentSplit env1 env2 env ->
      EnvironmentSplitN [env1 ; env2] env
  | EnvSplitN : forall env env1 env2 env3 envList,
      EnvironmentSplit env1 env2 env3 ->
      EnvironmentSplitN (env3 :: envList) env ->
      EnvironmentSplitN (env1 :: env2 :: envList) env.


Lemma EnvironmentSplit_elems : forall env env1 env2,
  EnvironmentSplit env1 env2 env ->
  forall x, In (Some x) env <-> (In (Some x) env1) \/ (In (Some x) env2).
Proof.
  intros * Split.
  induction Split; simpl.
  - intuition.
  - simpl. intros x.
    split.
    + intros [xNone | xIn].
      * discriminate xNone.
      * apply IHSplit in xIn.
        destruct xIn as [In1 | In2].
        -- left. now right.
        -- right. now right.
    + intros [[xNone | xIn] | [xNone | xIn]];
      try (now left).
      * assert (In' : In (Some x) env1 \/ In (Some x) env2). now left.
        rewrite <- IHSplit in In'.
        now right.
      * assert (In' : In (Some x) env1 \/ In (Some x) env2). now right.
        rewrite <- IHSplit in In'.
        now right.
  - intros y; split.
    + intros [ySome | yIn].
      * left; now left.
      * rewrite IHSplit in yIn.
        destruct yIn as [In1 | In2]; intuition.
    + intros [[ySome | yIn] | [yNone | yIn]].
      * now left.
      * assert (In' : In (Some y) env1 \/ In (Some y) env2). now left.
        rewrite <- IHSplit in In'.
        intuition.
      * discriminate yNone.
      * assert (In' : In (Some y) env1 \/ In (Some y) env2). now right.
        rewrite <- IHSplit in In'.
        intuition.
  - intros y; split.
    + intros [ySome | yIn].
      * right; now left.
      * rewrite IHSplit in yIn.
        destruct yIn as [In1 | In2]; intuition.
    + intros [[ySome | yIn] | [yNone | yIn]].
      * now left.
      * assert (In' : In (Some y) env1 \/ In (Some y) env2). now left.
        rewrite <- IHSplit in In'.
        intuition.
      * now left.
      * assert (In' : In (Some y) env1 \/ In (Some y) env2). now right.
        rewrite <- IHSplit in In'.
        intuition.
Qed.

End environment_test.

Notation "Env1 ,, Env2 ~= Env" := (EnvironmentSplit Env1 Env2 Env) (at level 80) : environment_scope.

Section environment_properties.

Context `{M : IMessage Message}.

(* TODO: Remove if not needed anymore *)

(** This example shows that environment subtyping is not transitive, since the Unrestricted
    predicate is a syntactic check on a type, NOT a semantic one.
 *)
(*Example Example_trans1 : Some (! 𝟙 ^^ •) :: None :: nil ≤ₑ Some (! 𝟙 ^^ ◦) :: None :: nil.*)
(*Proof.*)
(*  repeat constructor;  apply MPInclusion_refl.*)
(*Qed.*)
(*Example Example_trans2 : Some (! 𝟙 ^^ ◦) :: None :: nil ≤ₑ None :: None :: nil.*)
(*Proof.*)
(*  repeat constructor;  apply MPInclusion_refl.*)
(*Qed.*)
(*Example Example_trans3 : ~ (Some (! 𝟙 ^^ •) :: None :: nil ≤ₑ None :: None :: nil).*)
(*Proof.*)
(*  intros N; inversion N; subst; inversion H2.*)
(*Qed.*)


Lemma EnvironmentSplit_EmptyEnv : forall env, EmptyEnv env -> env,, env ~= env.
Proof.
  induction env.
  - constructor.
  - intros Empty; inversion Empty; subst; constructor; now apply IHenv.
Qed.

Lemma EnvironmentSplit_create_EmptyEnv : forall env,
  env,, create_EmptyEnv env ~= env.
Proof.
  induction env.
  - constructor.
  - simpl; destruct a.
    + now apply EnvSplitLeft.
    + now apply EnvSplitNone.
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

(*Lemma lookup_False_cons : forall env,*)
(* (forall x, False <-> is_Some (lookup x (None :: env))) ->*)
(* (forall x, False <-> is_Some (lookup x env)).*)
(*Proof.*)
(*  intros * Eq x.*)
(*  now generalize (Eq (S x)).*)
(*Qed.*)

(*Lemma lookup_False_cons_Some : forall env T,*)
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

(* TODO: Merge both lemmas into one *)
(*Lemma lookup_False_EmptyEnv : forall env, (forall x, False <-> is_Some (lookup x env)) -> EmptyEnv env.*)
(*Proof.*)
(*  induction env; intros Eq.*)
(*  - constructor.*)
(*  - destruct a.*)
(*    + generalize (Eq 0); simpl; intuition.*)
(*    + constructor.*)
(*      reflexivity.*)
(*      apply IHenv. now apply lookup_False_cons.*)
(*Qed.*)

(*Lemma lookup_False_EmptyEnv' : forall env, EmptyEnv env -> (forall x, False <-> is_Some (lookup x env)) .*)
(*Proof.*)
(*  induction env; intros Empty.*)
(*  - intros x; now rewrite lookup_nil.*)
(*  - destruct a.*)
(*    + inversion Empty; subst; discriminate.*)
(*    + intros x; inversion Empty; subst.*)
(*      induction x.*)
(*      * easy.*)
(*      * simpl. now apply IHenv.*)
(*Qed.*)

(*Lemma lookup_False_SingletonEnv : forall env n,*)
(*  (forall x, n = x \/ False <-> is_Some (lookup x env)) -> SingletonEnv env.*)
(*Proof.*)
(*  induction env; intros * Eq.*)
(*  - induction n.*)
(*    + generalize (Eq 0); rewrite lookup_nil; intuition.*)
(*    + apply IHn.*)
(*      intros x.*)
(*      generalize (Eq (S x)). simpl.*)
(*      intros Eq'.*)
(*      rewrite lookup_nil.*)
(*      assert (H : S n = S x <-> n = x). lia.*)
(*      rewrite H in Eq'.*)
(*      assumption.*)
(*  - induction n.*)
(*    + destruct a.*)
(*      * generalize (lookup_False_cons_Some env t Eq).*)
(*        intros Eq'.*)
(*        simpl.*)
(*        now apply lookup_False_EmptyEnv.*)
(*      * generalize (Eq 0); simpl; intuition.*)
(*    + simpl.*)
(*      destruct a; simpl in *.*)
(*      * apply IHn.*)
(*        generalize (Eq 0).*)
(*        assert (H : S n = 0 <-> False). lia.*)
(*        simpl; rewrite H; intuition.*)
(*      * apply IHenv with (n := n).*)
(*        intros x.*)
(*        generalize (Eq (S x)). simpl.*)
(*        intros Eq'.*)
(*        assert (H : S n = S x <-> n = x). lia.*)
(*        now rewrite <- H.*)
(*Qed.*)

(*Lemma lookup_False_n : forall env n,*)
(*  (forall x : nat, n = x \/ False <-> is_Some (lookup x env)) ->*)
(*  exists T, lookup n env = Some T.*)
(*Proof.*)
(*  induction env; intros * Eq.*)
(*  - induction n.*)
(*    + generalize (Eq 0); simpl; intuition.*)
(*    + generalize (Eq (S n)). simpl. intuition.*)
(*  - induction n; simpl in *.*)
(*    + destruct a; simpl in *.*)
(*      * now exists t.*)
(*      * generalize (Eq 0); simpl. intuition.*)
(*    + destruct a; simpl in *.*)
(*      * generalize (Eq 0); simpl.*)
(*        assert (F : S n = 0 <-> False). lia.*)
(*        rewrite F; intuition.*)
(*      * apply IHenv.*)
(*        intros x.*)
(*        generalize (Eq (S x)); simpl; intro Eq'.*)
(*        assert (H : S n = S x <-> n = x). lia.*)
(*        now rewrite <- H.*)
(*Qed.*)

(*Lemma lookup_cons_None : forall x env T,*)
(*  lookup x (None :: env) = Some T ->*)
(*  lookup (x-1) env = Some T.*)
(*Proof.*)
(*  destruct x; simpl; intros * xLookup.*)
(*  - inversion xLookup.*)
(*  - now rewrite PeanoNat.Nat.sub_0_r.*)
(*Qed.*)

(*Lemma lookup_cons_None' : forall x env,*)
(*  x <> 0 ->*)
(*  lookup x (None :: env) = lookup (x-1) env.*)
(*Proof.*)
(*  destruct x; simpl; intros * xLookup.*)
(*  - intuition.*)
(*  - now rewrite PeanoNat.Nat.sub_0_r.*)
(*Qed.*)

(*Lemma SingletonEnv_lookup_eq : forall env x y T T',*)
(*  SingletonEnv env ->*)
(*  lookup x env = Some T ->*)
(*  lookup y env = Some T' ->*)
(*  x = y /\ T = T'.*)
(*Proof.*)
(*  intros * Singleton xLookup yLookup.*)
(*  revert x y xLookup yLookup.*)
(*  induction env.*)
(*  - inversion Singleton.*)
(*  - simpl in *.*)
(*    destruct a.*)
(*    + intros * xLookup yLookup.*)
(*      generalize (EmptyEnv_lookup env Singleton).*)
(*      intros nLookup.*)
(*      induction x, y; simpl in *;*)
(*      try (generalize (nLookup x); intros F; now rewrite F in xLookup);*)
(*      try (generalize (nLookup y); intros F; now rewrite F in yLookup);*)
(*      rewrite xLookup in yLookup; now inversion yLookup.*)
(*    + intros * xLookup yLookup.*)
(*      induction x,y; simpl in *;*)
(*      try (discriminate xLookup || discriminate yLookup).*)
(*      simpl in *; generalize (IHenv Singleton x y xLookup yLookup).*)
(*      intros [Eq1 Eq2]; split.*)
(*      * now f_equal.*)
(*      * assumption.*)
(*Qed.*)

(*Lemma SingletonEnv_lookup_None : forall env x T,*)
(*  SingletonEnv env ->*)
(*  lookup x env = Some T ->*)
(*  forall y, x <> y -> lookup y env = None.*)
(*Proof.*)
(*  induction env.*)
(*  - intuition; inversion H.*)
(*  - simpl. intros * Single Lookup.*)
(*    destruct a; simpl in *.*)
(*    + assert (H : x = 0).*)
(*      {*)
(*        induction x.*)
(*        - reflexivity.*)
(*        - simpl in *.*)
(*          apply EmptyEnv_lookup with (x := x) in Single.*)
(*          rewrite Single in Lookup.*)
(*          discriminate.*)
(*      }*)
(*      subst; simpl in *.*)
(*      intros ? Neq.*)
(*      destruct y. intuition.*)
(*      simpl.*)
(*      now apply EmptyEnv_lookup.*)
(*    + intros ? Neq.*)
(*      generalize (IHenv (x-1) T Single (lookup_cons_None x env T Lookup)).*)
(*      intros F.*)
(*      destruct y.*)
(*      * reflexivity.*)
(*      * simpl. apply F.*)
(*        intros X.*)
(*        assert (Ge : 0 < x).*)
(*        {*)
(*          induction x.*)
(*          - simpl in Lookup. discriminate.*)
(*          - lia.*)
(*        }*)
(*        lia.*)
(*Qed.*)

(*Fixpoint EnvironmentSubtype_diff (env1 env2 : Env) : Env :=*)
(*  match env1, env2 with*)
(*  | nil, nil => nil*)
(*  | None :: env1', None :: env2' => None :: EnvironmentSubtype_diff env1' env2'*)
(*  | Some T :: env1', None :: env2' => Some T :: EnvironmentSubtype_diff env1' env2'*)
(*  | Some T :: env1', Some T' :: env2' => None :: EnvironmentSubtype_diff env1' env2'*)
(*  (* This should never occur when env1 ≤ₑ env2 *)*)
(*  | _, _ => nil*)
(*  end.*)

(* TODO: Remove? Do not know if this holds *)
(*Lemma EnvironmentSubtype_diff_CruftEnv : forall env1 env2,*)
(*  env1 ≤ₑ env2 ->*)
(*  CruftEnv (EnvironmentSubtype_diff env1 env2).*)
(*Proof.*)
(*  intros * Sub; induction Sub; try (now constructor).*)
(*  - simpl. constructor.*)
(*    + now apply Unrestricted_implies_Cruft.*)
(*    + assumption.*)
(*  - admit.*)
(*Admitted.*)

(*Fixpoint EnvironmentSubtype_diff_Sub (env1 env2 : Env) : Env :=*)
(*  match env1, env2 with*)
(*  | nil, nil => nil*)
(*  | None :: env1', None :: env2' => None :: EnvironmentSubtype_diff_Sub env1' env2'*)
(*  | Some T :: env1', None :: env2' => None :: EnvironmentSubtype_diff_Sub env1' env2'*)
(*  | Some T :: env1', Some T' :: env2' => Some T :: EnvironmentSubtype_diff_Sub env1' env2'*)
(*  (* This should never occur when env1 ≤ₑ env2 *)*)
(*  | _, _ => nil*)
(*  end.*)
(**)

(*Lemma EnvironmentSubtype_diff_Sub_Unrestricted : forall env1 env2 env2A env2B,*)
(*  env1 ≤ₑ env2 ->*)
(*  env2A,, env2B ~= env2 ->*)
(*  UnrestrictedEnv env2B ->*)
(*  UnrestrictedEnv (EnvironmentSubtype_diff_Sub env1 env2B).*)
(*Proof.*)
(*  intros * Sub.*)
(*  revert env2A env2B.*)
(*  induction Sub; intros * Split Unr.*)
(*  - inversion Split; subst; simpl; constructor.*)
(*  - inversion Split; subst; simpl.*)
(*    inversion Unr; subst.*)
(*    constructor.*)
(*    apply I.*)
(*    now apply IHSub with (env2A := env0).*)
(*  - inversion Split; subst; simpl.*)
(*    inversion Unr; subst.*)
(*    constructor.*)
(*    assumption.*)
(*    now apply IHSub with (env2A := env0).*)
(*  - inversion Split; subst; simpl; inversion Unr; subst.*)
(*    + constructor.*)
(*      apply I.*)
(*      now apply IHSub with (env2A := env0).*)
(*    + constructor.*)
(*      * now apply Subtype_preserves_Unrestricted with (T2 := T2).*)
(*      * now apply IHSub with (env2A := env0).*)
(*Qed.*)

(*Lemma EnvironmentSubtype_diff_split : forall env1 env2,*)
(*  env1 ≤ₑ env2 ->*)
(*  (EnvironmentSubtype_diff_Sub env1 env2),, (EnvironmentSubtype_diff env1 env2) ~= env1.*)
(*Proof.*)
(*  intros * Sub; induction Sub; simpl; now constructor.*)
(*Qed.*)

(*Lemma EnvironmentSubtype_diff_split2 : forall env1 env2 env2A env2B,*)
(*  env1 ≤ₑ env2 ->*)
(*  env2A,, env2B ~= env2 ->*)
(*  EnvironmentSplitN [EnvironmentSubtype_diff_Sub env1 env2A; EnvironmentSubtype_diff_Sub env1 env2B; EnvironmentSubtype_diff env1 env2] env1.*)
(*Proof.*)
(*  intros * Sub.*)
(*  revert env2A env2B.*)
(*  induction Sub; intros * Split.*)
(*  - inversion Split; subst; simpl.*)
(*    apply EnvSplitN with (env3 := []); repeat constructor.*)
(*  - inversion Split; subst; simpl.*)
(*    apply IHSub in H2.*)
(*    inversion H2; subst.*)
(*    inversion H5; subst.*)
(*    + econstructor.*)
(*      * assert (H : None :: EnvironmentSubtype_diff_Sub env1 env0,,*)
(*                  None :: EnvironmentSubtype_diff_Sub env1 env3 ~= None :: env6).*)
(*        now constructor.*)
(*        apply H.*)
(*      * now repeat constructor.*)
(*    + econstructor.*)
(*      * assert (H : None :: EnvironmentSubtype_diff_Sub env1 env0,,*)
(*                  None :: EnvironmentSubtype_diff_Sub env1 env3 ~= None :: env6).*)
(*        now constructor.*)
(*        apply H.*)
(*      * inversion H7.*)
(*  - inversion Split; subst; simpl.*)
(*    apply IHSub in H3.*)
(*    inversion H3; subst.*)
(*    inversion H6; subst.*)
(*    + apply EnvSplitN with (env3 := None :: env6).*)
(*      * now constructor.*)
(*      * now repeat constructor.*)
(*    + inversion H8.*)
(*  - inversion Split; subst; simpl.*)
(*    + apply IHSub in H3.*)
(*      inversion H3; subst.*)
(*      inversion H6; subst.*)
(*      * apply EnvSplitN with (env3 := Some T1 :: env6).*)
(*        -- now constructor.*)
(*        -- now repeat constructor.*)
(*      * inversion H8.*)
(*    + apply IHSub in H3.*)
(*      inversion H3; subst.*)
(*      inversion H6; subst.*)
(*      * apply EnvSplitN with (env3 := Some T1 :: env6).*)
(*        -- now constructor.*)
(*        -- now repeat constructor.*)
(*      * inversion H8.*)
(*Qed.*)

(*Lemma EnvironmentSubtype_diff_Sub_Empty : forall env1 env2,*)
(*  EmptyEnv env2 ->*)
(*  EmptyEnv (EnvironmentSubtype_diff_Sub env1 env2).*)
(*Proof.*)
(*  intros *.*)
(*  revert env1.*)
(*  induction env2; intros * Empty.*)
(*  - destruct env1.*)
(*    assumption.*)
(*    now destruct o.*)
(*  - destruct a; inversion Empty; subst.*)
(*    + discriminate.*)
(*    + destruct env1.*)
(*      * constructor.*)
(*      * destruct o; simpl; constructor; try reflexivity; now apply IHenv2.*)
(*Qed.*)

(*Lemma EnvironmentSubtype_diff_Sub_Singleton : forall env1 env2,*)
(*  env1 ≤ₑ env2 ->*)
(*  SingletonEnv env2 ->*)
(*  SingletonEnv (EnvironmentSubtype_diff_Sub env1 env2).*)
(*Proof.*)
(*  intros * Sub Single.*)
(*  induction Sub; simpl in *.*)
(*  - inversion Single.*)
(*  - now apply IHSub.*)
(*  - now apply IHSub.*)
(*  - now apply EnvironmentSubtype_diff_Sub_Empty.*)
(*Qed.*)

(*Lemma EnvironmentSubtype_diff_Sub_Singleton_Split : forall env1 env2 env2A env2B,*)
(*  env1 ≤ₑ env2 ->*)
(*  env2A,, env2B ~= env2 ->*)
(*  SingletonEnv env2A ->*)
(*  SingletonEnv (EnvironmentSubtype_diff_Sub env1 env2A).*)
(*Proof.*)


(*Lemma EnvironmentSubtype_diff_Sub_lookup : forall env1 env2 v T,*)
(*  env1 ≤ₑ env2 ->*)
(*  lookup v env2 = Some T ->*)
(*  exists T', lookup v (EnvironmentSubtype_diff_Sub env1 env2) = Some T'.*)
(*Proof.*)
(*  intros * Sub.*)
(*  revert v.*)
(*  induction Sub; simpl in *; intros * Lookup.*)
(*  - rewrite lookup_nil in Lookup; discriminate.*)
(*  - destruct v.*)
(*    + simpl in *. discriminate.*)
(*    + apply lookup_cons_None in Lookup.*)
(*      apply IHSub in Lookup.*)
(*      destruct Lookup as [T' Eq].*)
(*      exists T'.*)
(*      rewrite lookup_cons_None'.*)
(*      assumption.*)
(*      lia.*)
(*  - destruct v.*)
(*    + simpl in *. discriminate.*)
(*    + apply lookup_cons_None in Lookup.*)
(*      apply IHSub in Lookup.*)
(*      destruct Lookup as [T' Eq].*)
(*      exists T'.*)
(*      rewrite lookup_cons_None'.*)
(*      assumption.*)
(*      lia.*)
(*  - destruct v.*)
(*    + now exists T1.*)
(*    + simpl in *. now apply IHSub.*)
(*Qed.*)

(* TODO: Remove this if not needed *)

(*Fixpoint size (env : Env) : nat :=*)
(*  match env with*)
(*  | nil => 0*)
(*  | Some _ :: env' => S (size env')*)
(*  | None :: env' => size env'*)
(*  end.*)
(**)
(*Definition TTest (x y : option TUsage) :=*)
(*  match x with*)
(*  | Some x' => match y with*)
(*               | Some y' => x' ≤ y'*)
(*               | None => Unrestricted x'*)
(*               end*)
(*  | None => match y with*)
(*               | Some y' => False*)
(*               | None => True*)
(*               end*)
(*  end.*)
(**)
(*Lemma Unrestricted_dec : forall T, {Unrestricted T} + {~ Unrestricted T}.*)
(*Proof.*)
(*  intros *.*)
(*  destruct T.*)
(*  - left; constructor.*)
(*  - destruct m; destruct m; destruct u;*)
(*    try (right; unfold not; intros Un; inversion Un; fail).*)
(*    left; constructor.*)
(*Qed.*)
(**)
(*Fixpoint get_Unrestricted (env : Env) : Env :=*)
(*  match env with*)
(*  | nil => nil*)
(*  | None :: env' => None :: get_Unrestricted env'*)
(*  | Some T :: env' => if Unrestricted_dec T*)
(*                      then Some T :: get_Unrestricted env'*)
(*                      else None :: get_Unrestricted env'*)
(*  end.*)
(**)
(**)
(*Lemma EnvironmentSubtype_inv : forall env1 env2,*)
(*  env1 ≤ₑ env2 ->*)
(*  env1 = env2 \/ size env1 > size env2 \/ Forall2 TTest env1 env2.*)
(*Proof.*)
(*  intros * Sub.*)
(*  induction Sub.*)
(*  - now left.*)
(*  - destruct IHSub as [Eq | [Size | Forall]].*)
(*    + subst. now left.*)
(*    + simpl. right. now left.*)
(*    + now repeat right.*)
(*  - destruct IHSub as [Eq | [Size | Forall]].*)
(*    + simpl. subst. right. left. constructor.*)
(*    + simpl. subst. right. left. lia.*)
(*    + simpl. now repeat right.*)
(*  - destruct IHSub as [Eq | [Size | Forall]].*)
(*    + subst. repeat right.*)
(*      * easy.*)
(*      (* TODO: Move to own lemma *)*)
(*      * induction env2.*)
(*        -- easy.*)
(*        -- inversion Sub; subst.*)
(*           ++ constructor. easy. now apply IHenv2.*)
(*           ++ constructor. easy. now apply IHenv2.*)
(*    + right. left. simpl. lia.*)
(*    + now repeat right.*)
(*Qed.*)

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

  Lemma EnvironmentCombination_insert : forall x env1 env2 env T,
    env1 ▷ₑ env2 ~= insert x T env ->
    exists env1' env2',
      (env1 = insert x T env1' /\ env2 = raw_insert x None env2') \/
      (env1 = raw_insert x None env1' /\ env2 = insert x T env2') \/
      exists T1 T2, (env1 = insert x T1 env1' /\ env2 = insert x T2 env2' /\ T1 ▷ T2 ~= T).
  Proof.
    induction x; intros * Comb.
    - rewrite raw_insert_zero in Comb.
      inversion Comb; subst; exists env0, env3.
      + left; now repeat rewrite raw_insert_zero.
      + right; left; now repeat rewrite raw_insert_zero.
      + repeat right; repeat rewrite raw_insert_zero.
        now exists T1, T2.
    - rewrite raw_insert_successor in *.
      destruct (lookup 0 env).
      + inversion Comb; subst.
        * apply IHx in H2;
          destruct H2 as [env1' [env2' [[Eq1 Eq2] | [[Eq1 Eq2] | [T1' [T2' [Eq1 [Eq2 Comb']]]]]]]];
          subst; exists (Some t :: env1'), (None :: env2');
          try (repeat right; exists T1', T2');
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_zero; auto.
        * apply IHx in H2;
          destruct H2 as [env1' [env2' [[Eq1 Eq2] | [[Eq1 Eq2] | [T1' [T2' [Eq1 [Eq2 Comb']]]]]]]];
          subst; exists (None :: env1'), (Some t :: env2');
          try (repeat right; exists T1', T2');
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_zero; auto.
        * apply IHx in H3;
          destruct H3 as [env1' [env2' [[Eq1 Eq2] | [[Eq1 Eq2] | [T1' [T2' [Eq1 [Eq2 Comb']]]]]]]];
          subst; exists (Some T1 :: env1'), (Some T2 :: env2');
          try (repeat right; exists T1', T2');
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_zero; auto.
      + inversion Comb; subst.
        apply IHx in H2;
        destruct H2 as [env1' [env2' [[Eq1 Eq2] | [[Eq1 Eq2] | [T1' [T2' [Eq1 [Eq2 Comb']]]]]]]];
        subst; exists (None :: env1'), (None :: env2');
        try (repeat right; exists T1', T2');
        repeat rewrite raw_insert_successor;
        repeat rewrite lookup_zero; auto.
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
      (env1 = insert x T env1' /\ env2 = raw_insert x None env2') \/
      (env1 = raw_insert x None env1' /\ env2 = insert x T env2') \/
      exists BT, (env1 = insert x (TUBase BT) env1' /\ env2 = insert x (TUBase BT) env2').
  Proof.
    induction x; intros * Comb.
    - rewrite raw_insert_zero in Comb.
      inversion Comb; subst; exists env0, env3.
      + left; now repeat rewrite raw_insert_zero.
      + right; left; now repeat rewrite raw_insert_zero.
      + repeat right; repeat rewrite raw_insert_zero. eauto using raw_insert_zero.
    - rewrite raw_insert_successor in *.
      destruct (lookup 0 env).
      + inversion Comb; subst.
        * apply IHx in H2;
          destruct H2 as [env1' [env2' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT [Eq1 Eq2 ]]]]]];
          subst;
          exists (Some t :: env1'), (None :: env2');
          try (repeat right; exists BT);
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_zero;
          eauto.
        * apply IHx in H2;
          destruct H2 as [env1' [env2' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT [Eq1 Eq2 ]]]]]];
          subst;
          exists (None :: env1'), (Some t :: env2');
          try (repeat right; exists BT);
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_zero;
          eauto.
        * apply IHx in H2;
          destruct H2 as [env1' [env2' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT' [Eq1 Eq2 ]]]]]];
          subst;
          exists (Some (TUBase BT) :: env1'), (Some (TUBase BT) :: env2');
          try (repeat right; exists BT');
          repeat rewrite raw_insert_successor;
          repeat rewrite lookup_zero;
          eauto.
      + inversion Comb; subst.
        apply IHx in H2;
        destruct H2 as [env1' [env2' [[Eq1 Eq2] | [[Eq1 Eq2] | [BT' [Eq1 Eq2 ]]]]]];
        subst; exists (None :: env1'), (None :: env2');
        try (repeat right; exists BT');
        repeat rewrite raw_insert_successor;
        repeat rewrite lookup_zero; auto.
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

  (*Lemma EnvironmentDis_Comb_rev' : forall env1 env2 env3 env1' env,*)
  (*  env1' ▷ₑ env3 ~= env ->*)
  (*  env1 +ₑ env2 ~= env1' ->*)
  (*  exists env2', env1 +ₑ env2' ~= env /\ env2 ▷ₑ env3 ~= env2'.*)
  (*Proof.*)
  (*  intros * Dis1; revert env1 env2;*)
  (*  induction Dis1; intros * Dis2; inversion Dis2; subst;*)
  (*  try match goal with*)
  (*  | H : ?env1 +ₑ ?env2 ~= ?env3 |- _ =>*)
  (*    apply IHDis1 in H; destruct H as [env3' [Dis1' Dis2']]*)
  (*  end;*)
  (*  eauto with environment.*)
  (*Qed.*)

  (*Lemma EnvironmentDis_Comb_inv : forall env1 env2 env3 env1' env,*)
  (*  env1 +ₑ env2 ~= env1' ->*)
  (*  env1' ▷ₑ env3 ~= env ->*)
  (*  exists env2', env1 +ₑ env2' ~= env /\ env2 ▷ₑ env3 ~= env2'.*)
  (*Proof.*)
  (*  intros * Dis.*)
  (*  revert env3 env.*)
  (*  induction Dis; intros * Comb.*)
  (*  - inversion Comb; subst; eauto with environment.*)
  (*  - inversion Comb; subst.*)
  (*    + apply IHDis in H0.*)
  (*      destruct H0 as [env3' [Comb' Dis']].*)
  (*      exists (None :: env3').*)
  (*      eauto with environment.*)
  (*    + apply IHDis in H0.*)
  (*      destruct H0 as [env3' [Comb' Dis']].*)
  (*      exists (Some T :: env3').*)
  (*      eauto with environment.*)
  (*  - inversion Comb; subst.*)
  (*    + apply IHDis in H3.*)
  (*      destruct H3 as [env3' [Comb' Dis']].*)
  (*      exists (None :: env3').*)
  (*      eauto with environment.*)
  (*    + *)

  (*Lemma EnvironmentSubtype_middle : forall env1_1 env1_2 env2 A,*)
  (*  env1_1 ++ Some A :: env1_2 ≤ₑ env2 ->*)
  (*  exists env2_1 env2_2,*)
  (*  (env2 = env2_1 ++ None :: env2_2) \/*)
  (*  exists A', (env2 = env2_1 ++ Some A' :: env2_2 /\ A ≤ A').*)
  (*Proof.*)
  (*  induction env1_1; simpl; intros * Sub.*)
  (*  - exists []; simpl.*)
  (*    remember (Some A :: env1_2) as E.*)
  (*    revert env1_2 A HeqE.*)
  (*    induction Sub; intros.*)
  (*    + discriminate.*)
  (*    + discriminate.*)
  (*    + inversion HeqE; subst. exists env2. now left.*)
  (*    + inversion HeqE; subst. exists env2. right. now exists T2.*)
  (*    + generalize (IHSub1 _ _ HeqE).*)
  (*      intros [env2_2 [Eq | [A' [Eq Sub]]]].*)
  (*      * subst. apply EnvironmentSubtype_None_inv in Sub2.*)
  (*        destruct Sub2 as [env2 Eq Sub].*)
  (*        exists env2; now left.*)
  (*      * subst.*)
  (*        generalize (IHSub2 _ _ eq_refl).*)
  (*        intros [env2_2' [Eq | [A'' [Eq Sub']]]].*)
  (*        -- exists env2_2'; now left.*)
  (*        -- subst. exists env2_2'; right; exists A''; constructor.*)
  (*           reflexivity.*)
  (*           eapply Subtype_trans; eassumption.*)
  (*    + subst. exists env1_2; right; exists A. constructor.*)
  (*      reflexivity. apply Subtype_refl.*)
  (*  - destruct a.*)
  (*    + apply EnvironmentSubtype_Some_inv in Sub.*)
  (*      destruct Sub as [env2' [[Eq EnvSub] | [T' [Eq [Sub EnvSub]]]]].*)
  (*      * exists nil, env2'; left. apply Eq.*)
  (*      * apply IHenv1_1 in EnvSub.*)
  (*        destruct EnvSub as [env2_1' [env2_2' [Eq' | [A' [Eq' Sub']]]]];*)
  (*        subst; exists (Some T' :: env2_1'), env2_2'.*)
  (*        -- now left.*)
  (*        -- right; now exists A'.*)
  (*    + apply EnvironmentSubtype_None_inv in Sub.*)
  (*      destruct Sub as [env2' [Eq EnvSub]].*)
  (*      apply IHenv1_1 in EnvSub.*)
  (*      destruct EnvSub as [env2_1' [env2_2' [Eq' | [A' [Eq' Sub']]]]];*)
  (*      subst; exists (None :: env2_1'), env2_2'.*)
  (*      * now left.*)
  (*      * right; now exists A'.*)
  (*Qed.*)


End environment_properties.

Hint Resolve create_EmptyEnv_EmptyEnv : environment.
Hint Resolve SubEnv_EmptyEnv_create_EmptyEnv : environment.
Hint Resolve EnvironmentSubtype_nil_left : environment.
Hint Resolve EnvironmentSubtype_nil_right : environment.
