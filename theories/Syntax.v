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
  | GReceive : Message -> list VarName -> VarName -> Term -> Guard.

Inductive FunctionDefinition : Type :=
  | FunDef : DefinitionName -> list TUsage -> TUsage -> Term -> FunctionDefinition.

Type EnvironmentDisjointCombinationN.

(* TODO: Put f and g into a typeclass? *)
(* TODO: Include body term in g *)
Inductive WellTypedTerm {f : Message -> list TType} {g : DefinitionName -> (list TUsage) * TUsage} : Env -> Term -> TUsage -> Prop :=
  (* Var *)
  | VAR   : forall v env T,
      lookup v env = Some T ->
      WellTypedTerm env (TValue (ValueVar (Var v))) T
  (* Consts *)
  | TRUE  : WellTypedTerm nil (TValue (ValueBool true)) (TUBase BTBool)
  | FALSE : WellTypedTerm nil (TValue (ValueBool false)) (TUBase BTBool)
  | UNIT  : WellTypedTerm nil (TValue ValueUnit) (TUBase BTUnit)
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
  | NEW : WellTypedTerm nil TNew (? 𝟙 ^^ •)
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
      WellTypedTerm (Some (? e ^^ •) :: (map (fun x => Some (secondType x)) tList) ++ env) t T ->
      (* TODO: Check if this makes sense with environments and variables *)
      WellTypedGuard env (GReceive m vList mailbox t) T (« m » ⊙ e).

Inductive WellTypedDefinition {f : Message -> list TType} {g : DefinitionName -> (list TUsage) * TUsage} : FunctionDefinition -> Prop :=
  | FUNDEF : forall defName argumentTypes body bodyType,
      @WellTypedTerm f g (map Some argumentTypes) body bodyType ->
      WellTypedDefinition (FunDef defName argumentTypes bodyType body).


(* Attempt at intrinsic typing. Kinda hard to work with *)
(*
Inductive WellTypedTerm {f : Message -> list TType}: Env -> TUsage -> Prop :=
  (* Var *)
  (* Consts *)
    TRUE  : WellTypedTerm nil (TUBase BTBool)
  | FALSE : WellTypedTerm nil (TUBase BTBool)
  (* App *)
  (* Let *)
  | LET   : forall env1 env2 env T1 T2,
      env1 ▷ₑ env2 ~= env ->
      WellTypedTerm env1 ⌊ T1 ⌋ ->
      WellTypedTerm (cons ⌊ T1 ⌋ env2) T2 ->
      WellTypedTerm env T2
  (* Spawn *)
  | SPAWN : forall env,
      WellTypedTerm env (TUBase BTUnit) ->
      WellTypedTerm ⌈ env ⌉ₑ (TUBase BTUnit)
  | NEW : WellTypedTerm nil (? 𝟙 ^^ •)
  (* New *)
  (* Send *)
  | SEND : forall env env' envList tList m,
      Value env' (! « m » ^^ ◦) ->
      f m = tList ->
      [ (env' :: envList) ]+ₑ ~= env ->
      WellTypedTerm env (TUBase BTUnit)
  (* Guard *)
  (* Sub *)
  | SUB : forall env1 env2 T1 T2,
      env1 ≤ₑ env2 ->
      T1 ≤ T2 ->
      WellTypedTerm env2 T1 ->
      WellTypedTerm env1 T2.
*)
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
      GReceive Put [ Var 1 ] (Var 0) (TApp FullFutureDef [ValueVar (Var 0) ; ValueVar (Var 1)])
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
  - constructor. simpl. f_equal.
  - constructor. apply RECEIVE with (tList := FutureMessageTypes Put).
    + easy.
    + right. constructor.
    + simpl.
      eapply APP
      with (argumentTypes := fst (FutureDefinitions FullFutureDef))
           (envList := ((Some (FullFutureType ^^ •) :: None :: None :: nil) :: (None :: Some (TUBase BTBool) :: None :: nil) :: nil)).
      * easy.
      * repeat constructor.
      * simpl. constructor.
        -- constructor. now simpl.
        -- constructor.
           ++ constructor. now simpl.
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


End Examples.
