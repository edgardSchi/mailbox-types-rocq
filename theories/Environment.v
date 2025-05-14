(** * Typing environments *)

From MailboxTypes Require Export Types.
From MailboxTypes Require Import Util.

Require Import Lists.List.
Import ListNotations.
Require Import Lia.

Generalizable All Variables.

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
Definition Env := list (option TUsage).

(** Lookup the type of an variable in an environment *)
Fixpoint lookup (n : nat) (env : Env) : option TUsage :=
  match n, env with
  | _, nil => None
  | 0, (None :: env') => None
  | 0, (Some T :: env') => Some T
  | S n', (_ :: env') => lookup n' env'
  end.

(** Convert a list of types to an environment. This reverses the list. *)
Definition toEnv (l : list TUsage) : Env :=
  map Some (rev l).

(** Definition 3.4 of environment subtyping.
    Subtyping of environments includes weakening for unrestricted types.
    This representation relates two environments of equal length, but
    they may contain different amounts of types
*)
Inductive EnvironmentSubtype : Env -> Env -> Prop :=
    EnvSubtypeEmpty : EnvironmentSubtype nil nil
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
      EnvironmentSubtype (Some T1 :: env1) (Some T2 :: env2).

(** Strict environment subtyping.
    Strict subtyping of environments is same as normal
    subtyping but the domains of both environments must be
    equal. In our representation this means that for every
    index in every list, both contain either None or Some.
*)
Inductive EnvironmentSubtypeStrict : Env -> Env -> Prop :=
    EnvSubtypeStrEmpty : EnvironmentSubtypeStrict nil nil
  | EnvSubtypeStrNone : forall env1 env2,
      EnvironmentSubtypeStrict env1 env2 ->
      EnvironmentSubtypeStrict (None :: env1) (None :: env2)
  | EnvSubtypeStrSub : forall env1 env2 T1 T2,
      Subtype T1 T2 ->
      EnvironmentSubtypeStrict env1 env2 ->
      EnvironmentSubtypeStrict (Some T1 :: env1) (Some T2 :: env2).


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


(** An empty environment contains only None as entries *)
Definition EmptyEnv (e : Env) : Prop := Forall (fun x => x = None) e.

(** A singleton environment contains only a single type *)
Fixpoint SingletonEnv (e : Env) : Prop :=
  match e with
  | nil => False
  | None :: e' => SingletonEnv e'
  | (Some _) :: e' => EmptyEnv e'
  end.

(** Creates an empty environment based on the size of the provided environment *)
Fixpoint create_EmptyEnv (e : Env) : Env :=
  match e with
  | nil => nil
  | t :: e' => None :: create_EmptyEnv e'
  end.

End environment_def.

(** Notation for environments *)
Declare Scope environment_scope.
Open Scope environment_scope.

Notation "Env1 ≤ₑ Env2" := (EnvironmentSubtype Env1 Env2) (at level 80) : environment_scope.
Notation "Env1 ≼ₑ Env2" := (EnvironmentSubtypeStrict Env1 Env2) (at level 80) : environment_scope.
Notation "Env1 ▷ₑ Env2 ~= Env" := (EnvironmentCombination Env1 Env2 Env) (at level 80) : environment_scope.
Notation "Env1 +ₑ Env2 ~= Env" := (EnvironmentDisjointCombination Env1 Env2 Env) (at level 80) : environment_scope.
(* TODO: Change the below notation. It sometimes collides with list notations *)
Notation "[ Env1 ]+ₑ ~= Env" := (EnvironmentDisjointCombinationN Env1 Env) (at level 80) : environment_scope.
Notation "⌊ Env ⌋ₑ" := (returnEnvironment Env) : environment_scope.
Notation "⌈ Env ⌉ₑ" := (secondEnvironment Env) : environment_scope.

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
    + now apply IHenv.
Qed.

Lemma lookup_nil : forall x, lookup x [] = None.
Proof.
  now destruct x.
Qed.

Lemma lookup_False_cons : forall env,
 (forall x, False <-> is_Some (lookup x (None :: env))) ->
 (forall x, False <-> is_Some (lookup x env)).
Proof.
  intros * Eq x.
  now generalize (Eq (S x)).
Qed.

Lemma lookup_False_cons_Some : forall env T,
  (forall x, 0 = x \/ False <-> is_Some (lookup x (Some T :: env))) ->
  (forall x, False <-> is_Some (lookup x env)).
Proof.
  intros * Eq x.
  generalize (Eq (S x)).
  intros EqX.
  destruct x.
  - intuition. discriminate H0.
  - intuition. discriminate H0.
Qed.

(* TODO: Merge both lemmas into one *)
Lemma lookup_False_EmptyEnv : forall env, (forall x, False <-> is_Some (lookup x env)) -> EmptyEnv env.
Proof.
  induction env; intros Eq.
  - constructor.
  - destruct a.
    + generalize (Eq 0); simpl; intuition.
    + constructor.
      reflexivity.
      apply IHenv. now apply lookup_False_cons.
Qed.

Lemma lookup_False_EmptyEnv' : forall env, EmptyEnv env -> (forall x, False <-> is_Some (lookup x env)) .
Proof.
  induction env; intros Empty.
  - intros x; now rewrite lookup_nil.
  - destruct a.
    + inversion Empty; subst; discriminate.
    + intros x; inversion Empty; subst.
      induction x.
      * easy.
      * simpl. now apply IHenv.
Qed.

Lemma lookup_False_SingletonEnv : forall env n,
  (forall x, n = x \/ False <-> is_Some (lookup x env)) -> SingletonEnv env.
Proof.
  induction env; intros * Eq.
  - induction n.
    + generalize (Eq 0); rewrite lookup_nil; intuition.
    + apply IHn.
      intros x.
      generalize (Eq (S x)). simpl.
      intros Eq'.
      rewrite lookup_nil.
      assert (H : S n = S x <-> n = x). lia.
      rewrite H in Eq'.
      assumption.
  - induction n.
    + destruct a.
      * generalize (lookup_False_cons_Some env t Eq).
        intros Eq'.
        simpl.
        now apply lookup_False_EmptyEnv.
      * generalize (Eq 0); simpl; intuition.
    + simpl.
      destruct a; simpl in *.
      * apply IHn.
        generalize (Eq 0).
        assert (H : S n = 0 <-> False). lia.
        simpl; rewrite H; intuition.
      * apply IHenv with (n := n).
        intros x.
        generalize (Eq (S x)). simpl.
        intros Eq'.
        assert (H : S n = S x <-> n = x). lia.
        now rewrite <- H.
Qed.

Lemma lookup_False_n : forall env n,
  (forall x : nat, n = x \/ False <-> is_Some (lookup x env)) ->
  exists T, lookup n env = Some T.
Proof.
  induction env; intros * Eq.
  - induction n.
    + generalize (Eq 0); simpl; intuition.
    + generalize (Eq (S n)). simpl. intuition.
  - induction n; simpl in *.
    + destruct a; simpl in *.
      * now exists t.
      * generalize (Eq 0); simpl. intuition.
    + destruct a; simpl in *.
      * generalize (Eq 0); simpl.
        assert (F : S n = 0 <-> False). lia.
        rewrite F; intuition.
      * apply IHenv.
        intros x.
        generalize (Eq (S x)); simpl; intro Eq'.
        assert (H : S n = S x <-> n = x). lia.
        now rewrite <- H.
Qed.


Lemma lookup_cons_None : forall x env T,
  lookup x (None :: env) = Some T ->
  lookup (x-1) env = Some T.
Proof.
  destruct x; simpl; intros * xLookup.
  - inversion xLookup.
  - now rewrite PeanoNat.Nat.sub_0_r.
Qed.

Lemma lookup_cons_None' : forall x env,
  x <> 0 ->
  lookup x (None :: env) = lookup (x-1) env.
Proof.
  destruct x; simpl; intros * xLookup.
  - intuition.
  - now rewrite PeanoNat.Nat.sub_0_r.
Qed.

Lemma SingletonEnv_lookup_eq : forall env x y T T',
  SingletonEnv env ->
  lookup x env = Some T ->
  lookup y env = Some T' ->
  x = y /\ T = T'.
Proof.
  intros * Singleton xLookup yLookup.
  revert x y xLookup yLookup.
  induction env.
  - inversion Singleton.
  - simpl in *.
    destruct a.
    + intros * xLookup yLookup.
      generalize (EmptyEnv_lookup env Singleton).
      intros nLookup.
      induction x, y; simpl in *;
      try (generalize (nLookup x); intros F; now rewrite F in xLookup);
      try (generalize (nLookup y); intros F; now rewrite F in yLookup);
      rewrite xLookup in yLookup; now inversion yLookup.
    + intros * xLookup yLookup.
      induction x,y; simpl in *;
      try (discriminate xLookup || discriminate yLookup).
      simpl in *; generalize (IHenv Singleton x y xLookup yLookup).
      intros [Eq1 Eq2]; split.
      * now f_equal.
      * assumption.
Qed.

Lemma SingletonEnv_lookup_None : forall env x T,
  SingletonEnv env ->
  lookup x env = Some T ->
  forall y, x <> y -> lookup y env = None.
Proof.
  induction env.
  - intuition; inversion H.
  - simpl. intros * Single Lookup.
    destruct a; simpl in *.
    + assert (H : x = 0).
      {
        induction x.
        - reflexivity.
        - simpl in *.
          apply EmptyEnv_lookup with (x := x) in Single.
          rewrite Single in Lookup.
          discriminate.
      }
      subst; simpl in *.
      intros ? Neq.
      destruct y. intuition.
      simpl.
      now apply EmptyEnv_lookup.
    + intros ? Neq.
      generalize (IHenv (x-1) T Single (lookup_cons_None x env T Lookup)).
      intros F.
      destruct y.
      * reflexivity.
      * simpl. apply F.
        intros X.
        assert (Ge : 0 < x).
        {
          induction x.
          - simpl in Lookup. discriminate.
          - lia.
        }
        lia.
Qed.

Fixpoint EnvironmentSubtype_diff (env1 env2 : Env) : Env :=
  match env1, env2 with
  | nil, nil => nil
  | None :: env1', None :: env2' => None :: EnvironmentSubtype_diff env1' env2'
  | Some T :: env1', None :: env2' => Some T :: EnvironmentSubtype_diff env1' env2'
  | Some T :: env1', Some T' :: env2' => None :: EnvironmentSubtype_diff env1' env2'
  (* This should never occur when env1 ≤ₑ env2 *)
  | _, _ => nil
  end.

Lemma EnvironmentSubtype_diff_CruftEnv : forall env1 env2,
  env1 ≤ₑ env2 ->
  CruftEnv (EnvironmentSubtype_diff env1 env2).
Proof.
  intros * Sub; induction Sub; simpl; try (now constructor).
  constructor.
  now apply Unrestricted_implies_TUCruft.
  assumption.
Qed.

Fixpoint EnvironmentSubtype_diff_Sub (env1 env2 : Env) : Env :=
  match env1, env2 with
  | nil, nil => nil
  | None :: env1', None :: env2' => None :: EnvironmentSubtype_diff_Sub env1' env2'
  | Some T :: env1', None :: env2' => None :: EnvironmentSubtype_diff_Sub env1' env2'
  | Some T :: env1', Some T' :: env2' => Some T :: EnvironmentSubtype_diff_Sub env1' env2'
  (* This should never occur when env1 ≤ₑ env2 *)
  | _, _ => nil
  end.

Lemma EnvironmentSubtype_diff_Sub_Empty : forall env1 env2,
  env1 ≤ₑ env2 ->
  EmptyEnv env2 ->
  EmptyEnv (EnvironmentSubtype_diff_Sub env1 env2).
Proof.
  intros * Sub Empty.
  induction Sub; simpl in *.
  - assumption.
  - inversion Empty; subst.
    constructor.
    assumption.
    now apply IHSub.
  - inversion Empty; subst.
    constructor.
    assumption.
    now apply IHSub.
  - inversion Empty; subst; discriminate.
Qed.

Lemma EnvironmentSubtype_diff_Sub_Singleton : forall env1 env2,
  env1 ≤ₑ env2 ->
  SingletonEnv env2 ->
  SingletonEnv (EnvironmentSubtype_diff_Sub env1 env2).
Proof.
  intros * Sub Single.
  induction Sub; simpl in *.
  - inversion Single.
  - now apply IHSub.
  - now apply IHSub.
  - now apply EnvironmentSubtype_diff_Sub_Empty.
Qed.

Lemma EnvironmentSubtype_diff_Sub_lookup : forall env1 env2 v T,
  env1 ≤ₑ env2 ->
  lookup v env2 = Some T ->
  exists T', lookup v (EnvironmentSubtype_diff_Sub env1 env2) = Some T'.
Proof.
  intros * Sub.
  revert v.
  induction Sub; simpl in *; intros * Lookup.
  - rewrite lookup_nil in Lookup; discriminate.
  - destruct v.
    + simpl in *. discriminate.
    + apply lookup_cons_None in Lookup.
      apply IHSub in Lookup.
      destruct Lookup as [T' Eq].
      exists T'.
      rewrite lookup_cons_None'.
      assumption.
      lia.
  - destruct v.
    + simpl in *. discriminate.
    + apply lookup_cons_None in Lookup.
      apply IHSub in Lookup.
      destruct Lookup as [T' Eq].
      exists T'.
      rewrite lookup_cons_None'.
      assumption.
      lia.
  - destruct v.
    + now exists T1.
    + simpl in *. now apply IHSub.
Qed.

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

Lemma EmptyEnv_SubEnv_EmptyEnv : forall env1 env2, EmptyEnv env1 -> env1 ≤ₑ env2 -> EmptyEnv env2.
Proof.
  induction env1; intros * Empty Sub.
  - inversion Sub; subst; constructor.
  - inversion Sub; subst.
    + inversion Empty; subst.
      constructor.
      reflexivity.
      now apply IHenv1.
    + inversion Empty; subst; discriminate.
    + inversion Empty; subst; discriminate.
Qed.

Lemma CruftEnv_EmptyEnv : forall env, EmptyEnv env -> CruftEnv env.
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
  intros * Empty; induction env.
  - constructor.
  - inversion Empty; subst; constructor; now apply IHenv.
Qed.

Lemma EnvironmentSubtypeStrict_refl : forall env, env ≼ₑ env.
Proof.
  induction env.
  - constructor.
  - destruct a; constructor; try (assumption); apply Subtype_refl.
Qed.

Lemma EnvironmentSubtype_refl : forall env, env ≤ₑ env.
Proof.
  induction env.
  - constructor.
  - destruct a; constructor; try (apply Subtype_refl || assumption).
Qed.

End environment_properties.
