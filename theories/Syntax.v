(** * Syntax of the Pat programming language *)

From MailboxTypes Require Import Types.
From MailboxTypes Require Import Environment.
From MailboxTypes Require Import Message.
From MailboxTypes Require Import Util.

Require Import Lists.List.
Import ListNotations.

Generalizable All Variables.

Section syntax_def.

Context `{M : IMessage Message}.

(** We define a set of definition names to avoid dealing with
    function names. We assume they are defined before the
    program is executed.
*)
Class IDefinitionName DefinitionName : Type :=
  {
    eq_dec : forall m n, {@eq DefinitionName m n} + {~ @eq DefinitionName m n}
  }.

Context `{D : IDefinitionName DefinitionName}.

(** A variable is just a natural number *)
Inductive VarName : Type := Var : nat -> VarName.

(** We associated values as relations between environments and types.
    Since variables are treated as values, we need a way to check what
    their type is.
*)
Inductive Value : Type :=
    ValueBool : bool -> Value
  | ValueUnit : Value
  | ValueVar  : VarName -> Value.

Inductive Term : Type :=
    TValue : Value -> Term
  | TLet   : Term -> Term -> Term
  | TApp   : DefinitionName -> list Value -> Term
  | TSpawn : Term -> Term
  | TNew   : Term
  | TSend  : Value -> Message -> list Value -> Term
  | TGuard : Value -> MPattern -> list Guard -> Term
with Guard : Type :=
    GFail : Guard
  | GFree : Term -> Guard
  (* TODO: Remove list of variables *)
  | GReceive : Message -> list VarName -> VarName -> Term -> Guard.

Inductive FunctionDefinition : Type :=
  | FunDef : DefinitionName -> list TUsage -> TUsage -> Term -> FunctionDefinition.

(* TODO: Put f and g into a typeclass? *)
(* TODO: Include body term in g *)
Inductive WellTypedTerm {f : Message -> list TType} {g : DefinitionName -> (list TUsage) * TUsage} : Env -> Term -> TUsage -> Prop :=
  (* Var *)
  | VAR   : forall v env T,
      SingletonEnv env ->
      lookup v env = Some T ->
      WellTypedTerm env (TValue (ValueVar (Var v))) T
  (* Consts *)
  | TRUE  : forall env,
      EmptyEnv env ->
      WellTypedTerm env (TValue (ValueBool true)) (TUBase BTBool)
  | FALSE : forall env,
      EmptyEnv env ->
      WellTypedTerm env (TValue (ValueBool false)) (TUBase BTBool)
  | UNIT  : forall env,
      EmptyEnv env ->
      WellTypedTerm env (TValue ValueUnit) (TUBase BTUnit)
  (* App *)
  | APP : forall env envList vList definition bodyType argumentTypes,
      g definition = (argumentTypes, bodyType) ->
      [ envList ]+ₑ ~= env ->
      Forall3 WellTypedTerm envList (map TValue vList) (argumentTypes) ->
      WellTypedTerm env (TApp definition vList) bodyType
  (* Let *)
  | LET   : forall env env1 env2 T1 T2 t1 t2, 
      env1 ▷ₑ env2 ~= env ->
      WellTypedTerm env1 t1 ⌊ T1 ⌋ ->
      WellTypedTerm (Some ⌊ T1 ⌋ :: env2) t2 T2 ->
      WellTypedTerm env (TLet t1 t2) T2
  (* Spawn *)
  | SPAWN : forall env t,
      WellTypedTerm env t (TUBase BTUnit) ->
      WellTypedTerm ⌈ env ⌉ₑ (TSpawn t) (TUBase BTUnit)
  (* New *)
  | NEW : forall env,
      EmptyEnv env ->
      WellTypedTerm env TNew (? 𝟙 ^^ •)
  (* Send *)
  (* TODO: Maybe try a recursive approach with this rule *)
  | SEND : forall env env' envList tList vList m v,
      WellTypedTerm env' (TValue v) (! « m » ^^ ◦) ->
      f m = tList ->
      [ (env' :: envList) ]+ₑ ~= env ->
      Forall3 WellTypedTerm envList (map TValue vList) (map secondType tList) ->
      WellTypedTerm env (TSend v m vList) (TUBase BTUnit)
  (* Guard TODO *)
  | GUARD : forall env env1 env2 guards v T e f,
      env1 +ₑ env2 ~= env ->
      WellTypedTerm env1 (TValue v) (? f ^^ •) ->
      WellTypedGuards env2 guards T f ->
      e ⊑ f ->
      (* TODO: Check if this is correct *)
      f ⊧ f ->
      WellTypedTerm env (TGuard v e guards) T
  (* Sub *)
  | SUB : forall t env1 env2 T1 T2,
      env1 ≤ₑ env2 ->
      T1 ≤ T2 ->
      WellTypedTerm env2 t T1 ->
      WellTypedTerm env1 t T2
with WellTypedGuards {f : Message -> list TType} {g : DefinitionName -> (list TUsage) * TUsage} : Env -> list Guard -> TUsage -> MPattern -> Prop :=
  | SINGLE : forall T e env g,
      WellTypedGuard env g T e ->
      WellTypedGuards env (g :: nil) T e
  | SEQ : forall T e es env guards g,
      WellTypedGuard env g T e ->
      WellTypedGuards env guards T es ->
      WellTypedGuards env (g :: guards) T (e ⊕ es)
with WellTypedGuard {f : Message -> list TType} {g : DefinitionName -> (list TUsage) * TUsage} : Env -> Guard -> TUsage -> MPattern -> Prop :=
  (* Fail *)
  | FAIL : forall t env, WellTypedGuard env GFail t 𝟘
  (* Free *)
  | FREE : forall t env T, WellTypedTerm env t T -> WellTypedGuard env (GFree t) T 𝟙
  (* Receive *)
  | RECEIVE : forall t m env T tList vList e mailbox,
      f m = tList ->
      BaseTypes tList \/ BaseEnv env ->
      WellTypedTerm ((toEnv (map secondType tList)) ++ [Some (? e ^^ •)] ++ env) t T ->
      (* TODO: Check if this makes sense with environments and variables *)
      WellTypedGuard env (GReceive m vList mailbox t) T (« m » ⊙ e).

Inductive WellTypedDefinition {f : Message -> list TType} {g : DefinitionName -> (list TUsage) * TUsage} : FunctionDefinition -> Prop :=
  | FUNDEF : forall defName argumentTypes body bodyType,
      @WellTypedTerm f g (toEnv argumentTypes) body bodyType ->
      WellTypedDefinition (FunDef defName argumentTypes bodyType body).

End syntax_def.

Section Examples.

Inductive Future : Type :=
  | Put   : Future
  | Get   : Future
  | Reply : Future.

Instance FutureMessage : IMessage Future.
Proof.
  constructor;
  destruct m; destruct n;
  try (now left);
  try (now right).
Defined.

Inductive FutureDefinition : Type :=
  | EmptyFutureDef : FutureDefinition
  | FullFutureDef  : FutureDefinition
  | ClientDef      : FutureDefinition.

Instance FutureDefinitionName : IDefinitionName FutureDefinition.
Proof.
  constructor; destruct m; destruct n;
  try (now left);
  try (now right).
Defined.

Definition ClientSendType : @MType Future FutureMessage :=
  ! « Reply ».

Definition ClientReceiveType : @MType Future FutureMessage :=
  ? « Reply ».

Definition EmptyFutureType : @MType Future FutureMessage :=
  ? (« Put » ⊙ (⋆ « Get »)).

Definition FullFutureType : @MType Future FutureMessage :=
  ? ⋆ « Get ».

Definition FutureDefinitions (d : FutureDefinition) : (list TUsage) * TUsage :=
  match d with
  | EmptyFutureDef => (((EmptyFutureType ^^ •) :: nil), (TUBase BTUnit))
  | FullFutureDef => (((FullFutureType ^^ •) :: (TUBase BTBool) :: nil), (TUBase BTUnit))
  | ClientDef => (nil, (TUBase BTUnit))
  end.

Definition FutureMessageTypes (m : Future) : list TType :=
  match m with
  | Reply => TTBase BTBool :: nil
  | Put   => TTBase BTBool :: nil
  | Get   => TTMailbox (! « Reply ») :: nil
  end.

(** Definition of the function emptyFuture from the paper
    emptyFuture : EmptyFutureType -> 1
*)
Definition EmptyFuture : @FunctionDefinition Future FutureMessage FutureDefinition :=
  FunDef EmptyFutureDef [ EmptyFutureType ^^ • ] (TUBase BTUnit)
    (TGuard (ValueVar (Var 0)) (« Put » ⊙ (⋆ « Get »)) [
      GReceive Put [ Var 0 ] (Var 1) (TApp FullFutureDef [ValueVar (Var 1) ; ValueVar (Var 0)])
    ]).

(** Function emptyFuture is well-typed
    |- emptyFuture
*)
Lemma EmptyFutureWellTyped :
  @WellTypedDefinition Future FutureMessage FutureDefinition
    FutureMessageTypes FutureDefinitions EmptyFuture.
Proof.
  constructor.
  eapply GUARD with (env2 := (None :: nil)) (env1 := (Some (EmptyFutureType ^^ •)) :: nil) (f := (« Put » ⊙ (⋆ « Get »))).
  - simpl. repeat constructor.
  - constructor; simpl. constructor. f_equal.
  - constructor. apply RECEIVE with (tList := FutureMessageTypes Put).
    + easy.
    + right. constructor.
    + simpl.
      eapply APP
      with (argumentTypes := fst (FutureDefinitions FullFutureDef))
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

(** Definition of the function fullFuture from the paper
    fullFuture : FullFutureType -> 1
*)
Definition FullFuture : @FunctionDefinition Future FutureMessage FutureDefinition :=
  FunDef FullFutureDef [ FullFutureType ^^ • ; (TUBase BTBool) ] (TUBase BTUnit)
    (TGuard (ValueVar (Var 1)) (⋆ « Get ») [
      GFree (TValue ValueUnit) ;
      GReceive Get [ Var 0 ] (Var 1)
        (TLet
          (TSend (ValueVar (Var 0)) Reply [(ValueVar (Var 2))])
          (TApp FullFutureDef [ValueVar (Var 2) ; ValueVar (Var 3)])
        )
    ]).

(** Function emptyFuture is well-typed
    |- emptyFuture
*)
Lemma FullFutureWellTyped :
  @WellTypedDefinition Future FutureMessage FutureDefinition
    FutureMessageTypes FutureDefinitions FullFuture.
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

Definition Client : @FunctionDefinition Future FutureMessage FutureDefinition :=
  FunDef ClientDef [] (TUBase BTUnit)
    (TLet
      (TNew)
      (TLet
        (TSpawn (TApp EmptyFutureDef [ValueVar (Var 0)]))
        (TLet
          (TNew)
          (TLet
            (TSend (ValueVar (Var 1)) Put [ValueBool true])
            (TLet
              (TSend (ValueVar (Var 3)) Get [ValueVar (Var 2)])
              (TGuard (ValueVar (Var 3)) (« Reply ») [
                GReceive Reply [Var 0] (Var 3) (
                  (TLet
                    (TGuard (ValueVar (Var 4)) 𝟙 [(GFree (TValue (ValueVar (Var 4))))])
                    (TValue ValueUnit)
                  )
                )
              ]
              )
            )
          )
        )
      )
    ).

(*
Definition Client : @FunctionDefinition Future FutureMessage FutureDefinition :=
  FunDef ClientDef [] (TUBase BTUnit)
    (TLet
      (TLet
        (TNew)
        (TSpawn (TApp EmptyFutureDef [ValueVar (Var 0)]))
      )
      (TLet
        (TNew)
        (TLet
          (TSend (ValueVar (Var 1)) Put [ValueBool true])
          (TLet
            (TSend (ValueVar (Var 3)) Get [ValueVar (Var 2)])
            (TGuard (ValueVar (Var 3)) (« Reply ») [
              GReceive Reply [Var 0] (Var 3) (
                (TLet
                  (TGuard (ValueVar (Var 4)) 𝟙 [(GFree (TValue (ValueVar (Var 4))))])
                  (TValue ValueUnit)
                )
              )
            ]
            )
          )
        )
      )
    ).
*)

Lemma ClientWellTyped :
  @WellTypedDefinition Future FutureMessage FutureDefinition
    FutureMessageTypes FutureDefinitions Client.
Proof.
  constructor.
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
      * eapply LET with (T1 := TTBase BTUnit).
        (* TODO: Continue *)
Admitted.



End Examples.
