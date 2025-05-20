(** * Syntax of the Pat programming language *)

From MailboxTypes Require Import Types.
From MailboxTypes Require Import Environment.
From MailboxTypes Require Import Message.
From MailboxTypes Require Import Util.

Require Import Lists.List.
Import ListNotations.
Require Import Compare_dec.
Require Import ListSet.
Require Import PeanoNat.
Require Import Lia.

Require Fin.

Generalizable All Variables.

Section definition_def.

(** We define a set of definition names to avoid dealing with
    function names. We assume they are defined before the
    program is executed.
*)
Class IDefinitionName DefinitionName : Type :=
  {
    eq_dec : forall m n, {@eq DefinitionName m n} + {~ @eq DefinitionName m n}
  }.

End definition_def.

Section syntax_def.

Context `{M : IMessage Message}.
Context `{D : IDefinitionName DefinitionName}.

(** Finite data type inspired by Agda's version *)
Inductive Fin : nat -> Type :=
  | zero : forall {n}, Fin (S n)
  | succ : forall {n}, Fin n -> Fin (S n).

Fixpoint toNat {n} (f : Fin n) : nat :=
  match f with
  | zero => 0
  | succ f' => S (toNat f')
  end.

(* TODO: Check how this approach behaves with environments *)

(** Implementation of a finite type with n elements by iterating
    the option type n times.
    From the PhD thesis of Kathrin Stark
*)

(** A variable is just a natural number *)
Inductive VarName : Type := Var : nat -> VarName.

(** We associated values as relations between environments and types.
    Since variables are treated as values, we need a way to check what
    their type is.
*)
Inductive Value : nat -> Type :=
    ValueBool : forall n, bool -> Value n
  | ValueUnit : forall n, Value n
  | ValueVar  : forall {n}, Fin n -> Value n.

(** Terms of the language *)
Inductive Term `{IMessage Message} `{IDefinitionName DefinitionName} : nat -> Type :=
    TValue : forall {n}, Value n -> Term n
  | TLet   : forall {n}, Term n -> Term (S n) -> Term n
  | TApp   : forall {n}, DefinitionName -> list (Value n) -> Term n
  | TSpawn : forall {n}, Term n -> Term n
  | TNew   : forall {n}, Term n
  | TSend  : forall {n}, Value n -> Message -> list (Value n) -> Term n
  | TGuard : forall {n}, Value n -> MPattern -> list (Guard n) -> Term n
  with Guard `{IMessage Message} `{IDefinitionName DefinitionName} : nat -> Type :=
    GFail : forall {n}, Guard n
  | GFree : forall {n}, Term n -> Guard n
  | GReceive : forall {n} (m : Message), Fin n -> Term (n + content_size m) -> Guard n.

(*Fixpoint FV {n} (t : Term n) (depth : nat) : list (Fin n) :=*)
(*  match t with*)
(*  | var k =>*)
(*      (* Convert k to nat and check if it's >= depth *)*)
(*      if le_dec depth (proj1_sig (Fin.to_nat k)) then*)
(*        [Fin.of_nat_lt (Nat.sub_lt (Fin.to_nat k) depth (le_n_S depth _ (Fin.size_gt k)))] *)
(*      else*)
(*        []*)
(*  | lam t' => FV t' (S depth)  (* Enter binder: increment depth *)*)
(*  | app t1 t2 => FV t1 depth ++ FV t2 depth*)
(*  end.*)

Fixpoint set_concat (l : list (set nat)) : set nat :=
  match l with
  | nil => nil
  | (s :: l') => set_union Nat.eq_dec s (set_concat l')
  end.

Definition downShift (n : nat) := map (fun x => x - n).

Definition FV_val {n} (v : Value n) : set nat :=
  match v with
  | ValueVar x => (toNat x) :: nil
  | _ => nil
  end.

Fixpoint FV {n} (t : Term n) : set nat :=
  match t with
  | TValue v => FV_val v
  | TLet t1 t2  =>
      set_union Nat.eq_dec (FV t1) (downShift 1 (set_remove Nat.eq_dec 0 (FV t2)))
  | TApp _ values => set_concat (map (fun v => FV_val v) values)
  | TSpawn t1 => FV t1
  | TNew => nil
  | TSend v m values =>
      set_union Nat.eq_dec (FV_val v) (set_concat (map (fun v => FV_val v) values))
  | TGuard v _ guards =>
      set_union Nat.eq_dec (FV_val v) (set_concat (map (fun v => FV_guard v) guards))
  end
with FV_guard {n} (g : Guard n) : list nat :=
  match g with
  | GFail => nil
  | GFree t1 => FV t1
  | GReceive m x t1 =>
      set_union Nat.eq_dec [toNat x] (downShift (content_size m) (set_diff Nat.eq_dec (FV t1) (seq 0 ((content_size m)))))
  end.

Lemma FV_val_correct : forall n (v : Value n), length (FV_val v) <= n.
Proof.
  intros *.
  induction v; simpl.
  - lia.
  - lia.
  - inversion f; subst; lia.
Qed.

Lemma set_remove_length_le : forall r l n,
  length l <= n ->
  length (set_remove Nat.eq_dec r l) <= n.
Proof.
  intros r.
  induction l; simpl; intros * Leq.
  - assumption.
  - destruct (Nat.eq_dec r a) eqn:T.
    + subst. lia.
    + simpl.
      induction n.
      * lia.
      * apply le_n_S.
        apply IHl.
        lia.
Qed.

Lemma FV_correct : forall n (t : Term n), length (FV t) <= n.
Proof.
  induction t; simpl.
  - apply FV_val_correct.
  - generalize (set_remove_length_le 0 (FV t2) (S n) IHt2).
    intro LenRem2.
    assert (H : length (set_remove Nat.eq_dec 0 (FV t2)) <= n).
    {
      assert ()
      generalize (set_remove_length_le 0 (FV t2) n).
      inversion IHt2; subst.
      -generalize (set_remove_length_le 0 (FV t2) (S (S (n)))).
    }


(** Function definitions *)
Record FunctionDefinition : Type :=
  {
    name : DefinitionName
  ; argumentTypes : list TUsage
  ; returnType : TUsage
  ; body : Term (length argumentTypes)
  }.

(** A program is a collection of definitions, an initial term and a 
    mapping from message to types of the contents
    TODO: forall m, content_size m = length (signature m)
*)
Record Prog : Type :=
  {
    signature : Message -> list TType
  ; definitions : DefinitionName -> FunctionDefinition
  ; initialTerm : Term 0
  }.

End syntax_def.

Section future_example.

(** [Future] defines the message atoms *)
Inductive Future : Type :=
  | Put   : Future
  | Get   : Future
  | Reply : Future.

(** We show that [Future] has decidable equality *)
Instance FutureMessage : IMessage Future.
Proof.
  constructor.
  - destruct m; destruct n;
    try (now left);
    try (now right).
  - apply (fun _ => 1).
Defined.

(** Function definition names used in the program *)
Inductive FutureDefinition : Type :=
  | EmptyFutureDef : FutureDefinition
  | FullFutureDef  : FutureDefinition
  | ClientDef      : FutureDefinition.

(** We show that [FutureDefinitionName] has decidable equality *)
Instance FutureDefinitionName : IDefinitionName FutureDefinition.
Proof.
  constructor; destruct m; destruct n;
  try (now left);
  try (now right).
Defined.

(** We define the appropriate types used in the program *)
Definition ClientSendType : @MType Future FutureMessage :=
  ! « Reply ».

Definition ClientReceiveType : @MType Future FutureMessage :=
  ? « Reply ».

Definition EmptyFutureType : @MType Future FutureMessage :=
  ? (« Put » ⊙ (⋆ « Get »)).

Definition FullFutureType : @MType Future FutureMessage :=
  ? ⋆ « Get ».

(** Defining the signature of messages *)
Definition FutureMessageTypes (m : Future) : list TType :=
  match m with
  | Reply => TTBase BTBool :: nil
  | Put   => TTBase BTBool :: nil
  | Get   => TTMailbox (! « Reply ») :: nil
  end.


Definition AppTest : Term 2 :=
  (TApp FullFutureDef [ValueVar (succ zero) ; ValueVar (zero)]).

Definition Testt : Guard 1.
Proof.
  apply GReceive with (m := Put).
  - apply zero.
  - simpl.
    apply AppTest.
Qed.

Definition Testset : Term 1.
Proof.
  apply TGuard.
  - apply ValueVar. apply (zero).
  - apply (« Put » ⊙ (⋆ « Get »)).
  - apply cons.
    + apply GReceive with (m := Put).
      * apply zero.
      * simpl.
        apply TApp.
        -- apply FullFutureDef.
        -- apply [ValueVar (succ zero) ; ValueVar (zero)].
    + apply nil.
Qed.

Print Testset.

(** Definition of the function emptyFuture from the paper
    emptyFuture : EmptyFutureType -> 1
*)
Definition EmptyFutureBody : Term 1 :=
  TGuard (ValueVar zero) (« Put » ⊙ (⋆ « Get »)) [
    GReceive Put (zero)
      (TApp FullFutureDef [ValueVar (succ zero) ; ValueVar (zero)] : Term (1 + content_size Put))
  ].

Compute FV EmptyFutureBody.

Definition EmptyFuture : FunctionDefinition :=
  FunDef EmptyFutureDef [ EmptyFutureType ^^ • ] (TUBase BTUnit) EmptyFutureBody.

(** Definition of the function fullFuture from the paper
    fullFuture : FullFutureType -> 1
*)
Definition FullFutureBody : Term :=
  TGuard (ValueVar (Var 1)) (⋆ « Get ») [
    GFree (TValue ValueUnit) ;
    GReceive Get (Var 1)
      (TLet
        (TSend (ValueVar (Var 0)) Reply [(ValueVar (Var 2))])
        (TApp FullFutureDef [ValueVar (Var 2) ; ValueVar (Var 3)])
      )
  ].

Definition FullFuture : FunctionDefinition :=
  FunDef FullFutureDef [ FullFutureType ^^ • ; (TUBase BTBool) ] (TUBase BTUnit) FullFutureBody.

(** Definition of the function client from the paper
    client : 1
*)
Definition ClientBody : Term :=
  TLet
    (TNew)
    (TLet
      (TSpawn (TApp EmptyFutureDef [ValueVar (Var 0)]))
      (TLet
        (TNew)
        (TLet
          (TSend (ValueVar (Var 2)) Put [ValueBool true])
          (TLet
            (TSend (ValueVar (Var 3)) Get [ValueVar (Var 1)])
            (TGuard (ValueVar (Var 2)) (« Reply ») [
              GReceive Reply (Var 2) (
                (TLet
                  (TGuard (ValueVar (Var 1)) 𝟙 [(GFree (TValue ValueUnit))])
                  (TValue ValueUnit)
                )
              )]
            )
          )
        )
      )
    ).

Definition Client : FunctionDefinition :=
  FunDef ClientDef [] (TUBase BTUnit) ClientBody.

(** Defining the function returning function definitons *)
Definition FutureDefinitions (d : FutureDefinition) : FunctionDefinition :=
  match d with
  | EmptyFutureDef => FunDef EmptyFutureDef [EmptyFutureType ^^ •] (TUBase BTUnit) EmptyFutureBody
  | FullFutureDef => FunDef FullFutureDef [FullFutureType ^^ •; (TUBase BTBool)] (TUBase BTUnit) FullFutureBody
  | ClientDef => FunDef ClientDef [] (TUBase BTUnit) ClientBody
  end.

Definition FutureProgram :=
  {|
    signature := FutureMessageTypes
  ; definitions := FutureDefinitions
  ; initialTerm := ClientBody
  |}.

(** Function emptyFuture is well-typed
    |- emptyFuture
*)
Lemma EmptyFutureWellTyped :
  WellTypedDefinition FutureProgram EmptyFuture.
Proof.
  unfold EmptyFuture. unfold EmptyFutureBody.
  eapply FUNDEF; simpl.
  eapply GUARD with (env2 := (None :: nil)) (env1 := (Some (EmptyFutureType ^^ •)) :: nil) (f := (« Put » ⊙ ⋆ « Get »)).
  - simpl. repeat constructor.
  - constructor; simpl. constructor. f_equal.
  - constructor. apply RECEIVE with (tList := FutureMessageTypes Put).
    + easy.
    + right. constructor.
    + simpl.
      eapply APP with
        (envList := ((None :: Some (FullFutureType ^^ •) :: None :: nil) :: (Some (TUBase BTBool) :: None :: None :: nil) :: nil)).
      * easy.
      * repeat constructor.
      * simpl. constructor.
        -- constructor. simpl. repeat constructor. now simpl.
        -- constructor.
           ++ constructor. simpl. repeat constructor. now simpl.
           ++ constructor.
  - apply MPInclusion_refl.
  - constructor.
    eapply PNFLitComp.
    + apply MPResComp.
      * constructor.
      * constructor. constructor. easy.
    + rewrite MPComp_zero_left.
      rewrite MPComp_zero_right.
      rewrite MPComp_comm.
      rewrite MPComp_unit.
      now rewrite MPChoice_unit.
Qed.

(** Function emptyFuture is well-typed
    |- emptyFuture
*)
Lemma FullFutureWellTyped :
  WellTypedDefinition FutureProgram FullFuture.
Proof.
  constructor.
  simpl.
  eapply GUARD with
    (env1 := None :: Some (FullFutureType ^^ •) :: nil)
       (env2 := Some (TUBase BTBool) :: None :: nil)
    (f := 𝟙 ⊕ (« Get » ⊙ (⋆ « Get »))).
  - repeat constructor.
  - eapply SUB with (env2 := None :: Some (FullFutureType ^^ •) :: nil).
    + do 3 constructor.
      apply MPInclusion_refl.
      repeat constructor.
    + constructor.
      * apply MPStar_MPInclusion_rec.
      * constructor.
    + repeat constructor.
  - constructor.
    + constructor.
      eapply SUB with (env2 := None :: None :: nil) (T1 := TUBase BTUnit).
      * repeat constructor.
      * constructor.
      * apply UNIT. repeat constructor.
    + constructor.
      apply RECEIVE with (tList := FutureMessageTypes Get).
      * easy.
      * now right.
      * simpl. eapply LET with
        (env1 := Some (! « Reply » ^^ ◦) :: None :: Some (TUBase BTBool) :: None :: nil)
        (env2 := (None :: Some (? ⋆ « Get » ^^ •) :: Some (TUBase BTBool) :: None :: nil))
        (T1 := TTBase BTUnit).
        -- simpl. repeat constructor.
        -- simpl. eapply SEND with
           (env' := Some (! « Reply » ^^ ◦) :: None :: None :: None :: nil).
           ++ repeat constructor.
           ++ now simpl.
           ++ repeat constructor.
           ++ simpl. repeat constructor.
        -- simpl. apply SUB with
           (env2 := None :: None :: Some (? ⋆ « Get » ^^ •) :: Some (TUBase BTBool) :: None :: nil)
           (T1 := TUBase BTUnit).
           ** do 4 constructor.
              apply MPInclusion_refl.
              all: repeat constructor.
           ** constructor.
           ** eapply APP with
              (envList := (None :: None :: Some (? ⋆ « Get » ^^ •) :: None :: None :: nil)
               :: (None :: None :: None :: Some (TUBase BTBool) :: None :: nil) :: nil).
              --- easy.
              --- repeat constructor.
              --- repeat constructor.
  - apply MPStar_MPInclusion_rec.
  - constructor. constructor.
    + constructor.
    + eapply PNFLitComp.
      * repeat constructor.
      * rewrite MPComp_comm.
        rewrite MPComp_unit.
        rewrite MPChoice_comm.
        rewrite MPChoice_unit.
        apply MPStar_rec.
Qed.

Lemma ClientBodyWellTyped : WellTypedTerm FutureProgram [] ClientBody (TUBase BTUnit).
Proof.
  eapply LET with (T1 := TTMailbox (? 𝟙)); simpl.
  - constructor.
  - apply NEW; constructor.
  - eapply LET with (T1 := TTBase BTUnit); simpl.
    + apply EnvCombBoth with
        (T1 := ? ((« Put » ⊙  « Get ») ⊙  𝟙) ^^ ◦)
        (T2 := ! (« Put » ⊙  « Get ») ^^ •).
      * constructor.
      * constructor. constructor.
        apply TCombOutIn.
    + apply SUB with
        (T1 := TUBase BTUnit)
        (env2 := Some (? (« Put » ⊙  ⋆ « Get ») ^^ ◦) :: nil).
      * repeat constructor.
        (* TODO: Move into own lemma *)
        intros m mIn.
        rewrite MPComp_unit in mIn.
        inversion mIn; subst.
        eapply MPValueComp.
        apply H1.
        constructor. exists 1. simpl. rewrite MPComp_unit. apply H3.
        easy.
      * constructor.
      * assert (H : (Some (? « Put » ⊙ ⋆ « Get » ^^ ◦) :: nil) = ⌈ (Some (? « Put » ⊙ ⋆ « Get » ^^ •) :: nil) ⌉ₑ).
        { reflexivity. }
        rewrite H.
        apply SPAWN.
        eapply APP.
        -- easy.
        -- constructor.
        -- repeat constructor.
    + eapply LET with (T1 := TTMailbox (? 𝟙)) (env1 := None :: None :: nil). (*T1 := ? 𝟙 ^^ •).*)
      * repeat constructor.
      * simpl. 
        eapply SUB with (env2 := None :: None :: nil);
        repeat constructor.
        apply MPInclusion_refl.
      * eapply LET with
          (T1 := TTBase BTUnit)
          (env1 := None :: None :: Some (! « Put » ^^ ◦) :: nil).
        -- repeat constructor.
        -- eapply SEND with
             (env' := None :: None :: Some (! « Put » ^^ ◦) :: nil)
             (envList := (None :: None :: None :: nil) :: nil).
           ++ repeat constructor.
           ++ easy.
           ++ repeat constructor.
           ++ repeat constructor.
        -- eapply LET with
            (T1 := TTBase BTUnit)
            (env1 := None :: Some (! « Reply » ^^ ◦) :: None :: Some (! « Get » ^^ •) :: nil).
           ++ repeat constructor.
           ++ eapply SEND with
               (env' := None :: None :: None :: Some (! « Get » ^^ •) :: nil).
              ** eapply SUB with
                  (env2 := None :: None :: None :: Some (! « Get » ^^ ◦) :: nil).
                 --- repeat constructor. apply MPInclusion_refl.
                 --- constructor. apply MPInclusion_refl. constructor.
                 --- repeat constructor.
              ** easy.
              ** repeat constructor.
              ** repeat constructor.
           ++ eapply SUB with
                  (env2 := None :: None :: Some (? « Reply » ⊙ 𝟙 ^^ •) :: None :: None :: nil).
              ** repeat constructor. apply MPInclusion_refl.
              ** constructor.
              ** eapply GUARD with
                   (f := « Reply » ⊙ 𝟙) (env2 := None :: None :: None :: None :: None :: nil).
                 --- repeat constructor.
                 --- repeat constructor.
                 --- constructor. eapply RECEIVE.
                     +++ easy.
                     +++ right. constructor.
                     +++ simpl.
                         eapply LET with
                           (T1 := TTBase BTUnit)
                           (env1 := None :: Some (? 𝟙 ^^ •) :: None :: None :: None :: None :: None:: nil).
                           *** repeat constructor.
                           *** eapply GUARD.
                               ----  constructor. apply EnvDisCombLeft. repeat constructor.
                               ---- repeat constructor.
                               ---- repeat constructor.
                               ---- apply MPInclusion_refl.
                               ---- repeat constructor.
                           *** eapply SUB with
                                 (env2 := None :: None :: None :: None :: None :: None :: None :: None :: nil).
                               ---- repeat constructor.
                               ---- repeat constructor.
                               ---- repeat constructor.
                 --- intros m mIn. now rewrite MPComp_unit.
                 --- repeat constructor.
                     eapply PNFLitComp.
                     repeat constructor.
                     rewrite MPComp_unit.
                     rewrite MPComp_zero_right.
                     now rewrite MPChoice_unit.
Qed.

Lemma ClientWellTyped :
  WellTypedDefinition FutureProgram Client.
Proof.
  constructor.
  apply ClientBodyWellTyped.
Qed.

Lemma FutureProgramWellTyped : WellTypedProgram FutureProgram.
Proof.
  apply PROG.
  - destruct def; simpl.
    + apply EmptyFutureWellTyped.
    + apply FullFutureWellTyped.
    + apply ClientWellTyped.
  - simpl. apply ClientBodyWellTyped.
Qed.

Definition ExampleTerm :=
  TGuard (ValueVar (Var 0)) (⋆ « Get ») [
    GFree (TValue ValueUnit) ;
    GReceive Get (Var 1)
      (TLet
        (TSend (ValueVar (Var 0)) Reply [(ValueVar (Var 2))])
        (TApp FullFutureDef [ValueVar (Var 2) ; ValueVar (Var 3)])
      )
  ].


Compute FV FutureProgram ExampleTerm.
Compute FV FutureProgram EmptyFutureBody.
Compute FV FutureProgram FullFutureBody.
Compute FV FutureProgram ClientBody.

(*Example example1 : FV FutureProgram EmptyFutureBody = [0].*)
(*Proof.*)
(*  unfold EmptyFutureBody.*)
(*  Arguments FV : simpl nomatch.*)
(*  simpl.*)


End future_example.
