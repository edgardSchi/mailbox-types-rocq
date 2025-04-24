(** * Syntax of the Pat programming language *)

From MailboxTypes Require Import Types.
From MailboxTypes Require Import Environment.
From MailboxTypes Require Import Message.
From MailboxTypes Require Import Util.

Require Import Lists.List.
Import ListNotations.

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

(** Terms of the language *)
Inductive Term `{IMessage Message} `{IDefinitionName DefinitionName} : Type :=
    TValue : Value -> Term
  | TLet   : Term -> Term -> Term
  | TApp   : DefinitionName -> list Value -> Term
  | TSpawn : Term -> Term
  | TNew   : Term
  | TSend  : Value -> Message -> list Value -> Term
  | TGuard : Value -> MPattern -> list Guard -> Term
with Guard `{IMessage Message} `{IDefinitionName DefinitionName} : Type :=
    GFail : Guard
  | GFree : Term -> Guard
  | GReceive : Message -> VarName -> Term -> Guard.

(** Function definitions *)
Inductive FunctionDefinition : Type :=
  | FunDef : DefinitionName ->
             list TUsage ->
             TUsage ->
             Term ->
             FunctionDefinition.

(** A program is a collection of definitions, an initial term and a 
    mapping from message to types of the contents
*)
Record Prog : Type :=
  {
    signature : Message -> list TType
  (*; definitions : DefinitionName -> (list TUsage) * TUsage * Term*)
  ; definitions : DefinitionName -> FunctionDefinition
  ; initialTerm : Term
  }.

End syntax_def.
