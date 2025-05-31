(** * Substitution *)

From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.
From MailboxTypes Require Import TypingRules.


(** We assume functional extensionality in order to proof statements about substitutions. *)
From Stdlib Require Import FunctionalExtensionality.

Generalizable All Variables.

(** ** Definitions *)
Section subs_def.

  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

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

  Lemma sub_lemma : forall p env1 env2 env A A' B v t,
    WellTypedTerm p (Some A :: env1) t B ->
    WellTypedTerm p env2 (TValue v) A' ->
    A' ≤ A ->
    (None :: env1) +ₑ env2 ~= env ->
    WellTypedTerm p env (t[v..]) B.
  Proof.
    (*intros * WT1 WT2 Sub Dis.*)
    (*remember (Some A :: env1) as env1' eqn:E.*)
    (*generalize dependent env1.*)
    (*induction WT1 using @WellTypedTerm_ind3 with*)
    (*  (P0 := fun _ _ _ _ => True)*)
    (*  (P1 := fun _ _ _ _ => True).*)
    (*intros * WT1.*)
    (*revert env2 env v A'.*)
    (*remember (Some A :: env1) as env1' eqn:E.*)
    (*generalize dependent A.*)
    (*generalize dependent env1.*)
    (*induction WT1; intros.*)
    (*- simpl in *.*)
    (*  assert (zero : v = 0). admit.*)
    (*  assert (SubTy : T = A). admit.*)
    (*  subst. simpl.*)
    (*  (*rewrite subst_1_Var_0.*)*)
    (*  eapply SUB with (env2 := env2).*)
    (*  (* env1 is empty, thus env2 = env *)*)
    (*  admit.*)
    (*  apply H2.*)
    (*  apply H1.*)
    (*- inversion H; subst; discriminate.*)
    (*- inversion H; subst; discriminate.*)
    (*- inversion H; subst; discriminate.*)
    (*- eapply APP.*)
    (*  + apply H.*)
    (*  + eapply IHWT1. apply E. apply H0. assumption. assumption.*)
    (*- subst.*)
    (*  inversion H; subst.*)
    (*  + eapply LET.*)
    (*    * apply (EnvironmentDis_implies_Comb _ _ _ H2).*)
    (*    * eapply IHWT1_1.*)
    (*      -- reflexivity.*)
    (*      -- apply H0.*)
    (*      -- assumption.*)
    (*      -- admit.*)
    (*- admit.*)
    (*- subst; inversion H; subst; discriminate.*)
    (*- admit.*)
    (*- admit.*)
    (*- subst. inversion H3; subst; inversion H; subst.*)
    (*  + eapply SUB.*)
    (*    * apply EnvSubtypeRefl.*)
    (*    * apply H0.*)
    (*    * eapply IHWT1.*)
    (*      -- *)
    Admitted.

End subs_def.
