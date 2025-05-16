(** * Syntax of the Pat programming language *)

From MailboxTypes Require Import Types.
From MailboxTypes Require Import Environment.
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
  ; definitions : DefinitionName -> FunctionDefinition
  ; initialTerm : Term
  }.

End syntax_def.


From Stdlib Require Import ListSet.
From Stdlib Require Import PeanoNat.

Section free_var_def.

Context `{M : IMessage Message}.
Context `{D : IDefinitionName DefinitionName}.

Fixpoint set_concat (l : list (set nat)) : set nat :=
  match l with
  | nil => nil
  | (s :: l') => set_union Nat.eq_dec s (set_concat l')
  end.

(* TODO: Check if this construction of free variables is correct *)
(* TODO: Move this section to corresponding place when confirmed it works *)

(** Computes the set of free variables for a term.
    Based on the paper "HOπ in Coq" by Ambal et. al.
*)

Definition downShift (n : nat) := set_map Nat.eq_dec (fun x => x - n).

Definition FV_val (v : Value) : set nat :=
  match v with
  | ValueVar (Var x) => x :: nil
  | _ => nil
  end.

Fixpoint FV (t : Term) : set nat :=
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
with FV_guard (g : Guard) : list nat :=
  match g with
  | GFail => nil
  | GFree t1 => FV t1
  | GReceive m (Var x) t1 =>
      set_union Nat.eq_dec [x] (downShift (content_size m) (set_diff Nat.eq_dec (FV t1) (seq 0 ((content_size m)))))
  end.

End free_var_def.
