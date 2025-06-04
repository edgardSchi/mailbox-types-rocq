(** * Syntax of the Mailbox Calculus *)

From MailboxTypes Require Import Types.
From MailboxTypes Require Import Message.
From MailboxTypes Require Import Util.

From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Compare_dec.

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

Inductive Fin : nat -> Type :=
  | z : forall n, Fin (S n)
  | s : forall n, Fin n -> Fin (S n).

(** A variable is just a natural number bounded by some number n *)
Definition Name n := Fin n.

(** We associated values as relations between environments and types.
    Since variables are treated as values, we need a way to check what
    their type is.
*)
(*Inductive Value : Type :=*)
(*    ValueBool : bool -> Value*)
(*  | ValueUnit : Value*)
(*  | ValueVar  : Name -> Value.*)

Type pred.

(** Terms of the language *)
Inductive Process `{IMessage Message} `{IDefinitionName DefinitionName} (n : nat) : Type :=
  | PDone : Process n
  | PInv : DefinitionName -> Name n -> Process n
  | PGuard : Guard n -> Process n
  | PSend : Name n -> Message -> Name n -> Process n
  | PPar : Process n -> Process n -> Process n
  | PRes : Process (S n) -> Process n
  with Guard `{IMessage Message} `{IDefinitionName DefinitionName} (n : nat) : Type :=
  | GFail : Name n -> Guard n
  | GFree : Name n -> Process (pred n) -> Guard n
  | GReceive : Name n -> Message -> Name n -> Process (S n) -> Guard n
  | GComp : Guard n -> Guard n -> Guard n.

Arguments PDone {_} {_} {_}.

(** Function definitions *)
Inductive FunctionDefinition : Type :=
  | FunDef : DefinitionName ->  (* Function name *)
             TUsage ->          (* Argument type *)
             TUsage ->          (* Result type *)
             Process 1 ->            (* Function body *)
             FunctionDefinition.

(** A program is a collection of definitions, an initial term and a
    mapping from message to the content's type
*)
Record Prog : Type :=
  {
    signature : Message -> TType
  ; definitions : DefinitionName -> FunctionDefinition
  ; initialTerm : Process 0
  }.

(** Defining the mutual recursion scheme for [Process] *)
Scheme Process_ind2 := Induction for Process Sort Prop
  with Guard_ind2 := Induction for Guard Sort Prop.

End syntax_def.

Declare Scope process_scope.
Notation "'done'" := (PDone _) (at level 1).
Notation "X [ v ]" := (PInv _ X v) (at level 7, format "X '/' [ v ]").
(* TODO: Guard *)
Notation "u '!' '<' m '>[' v ']'" := (PSend _ u m v) (at level 7, format "u '/' ! '/' < m '/' >[ v ]").
Notation "A ∥ B" := (PPar _ A B) (at level 10).
Notation "'𝝂' P" := (PRes _ P) (at level 9).
Notation "'fail' u" := (GFail _ u) (at level 1).
Notation "'free' u ';' P" := (GFree _ u P) (at level 7).
Notation "u ? m ';' P" := (GReceive _ u m P) (at level 7).
Notation "G '|+|' H" := (GComp _ G H) (at level 10, left associativity).

Section Examples.

Context `{M : IMessage Message}.
Context `{D : IDefinitionName DefinitionName}.

Definition TestProcess : Process 0 := 𝝂 done.

(** [Future] defines the message atoms *)
Inductive Data : Type := data : Data.

(** We show that [Future] has decidable equality *)
Instance DataMessage : IMessage Data.
Proof.
  constructor.
  - destruct m; destruct n;
    try (now left);
    try (now right).
  - apply (fun _ => 1).
Defined.

Definition ExampleProcess : Process 0.
Proof.
  apply PRes.
  apply PRes.
  apply PRes.
  apply PGuard.
  apply GComp.
  + apply GFree. apply z. apply PDone.
  + apply GComp.
    apply GFree. apply z. apply PDone.
    apply GFree. apply z. apply PDone.
Defined.

Print ExampleProcess.

End Examples.

