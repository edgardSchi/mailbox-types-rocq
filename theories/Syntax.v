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
(*Inductive VarName : Type := Var : nat -> VarName.*)
Definition VarName := nat.

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
  | TApp   : DefinitionName -> Value -> Term
  | TSpawn : Term -> Term
  | TNew   : Term
  | TSend  : Value -> Message -> Value -> Term
  | TGuard : Value -> MPattern -> list Guard -> Term
with Guard `{IMessage Message} `{IDefinitionName DefinitionName} : Type :=
    GFail : Guard
  | GFree : Term -> Guard
  | GReceive : Message -> Term -> Guard.

(** Function definitions *)
Inductive FunctionDefinition : Type :=
  | FunDef : DefinitionName ->  (* Function name *)
             TUsage ->          (* Argument type *)
             TUsage ->          (* Result type *)
             Term ->            (* Function body *)
             FunctionDefinition.

(** A program is a collection of definitions, an initial term and a
    mapping from message to the content's type
*)
Record Prog : Type :=
  {
    signature : Message -> TType
  ; definitions : DefinitionName -> FunctionDefinition
  ; initialTerm : Term
  }.

(** Defining the mutual recursion scheme for [Term] *)
Scheme Term_ind2 := Induction for Term Sort Prop
  with Guard_ind2 := Induction for Guard Sort Prop.

End syntax_def.

Section term_ind.

  Context `{M : IMessage Message}.
  Context `{D : IDefinitionName DefinitionName}.

  Variable P : Term -> Prop.
  Variable PG : Guard -> Prop.

  Hypothesis TValue_case : forall v, P (TValue v).
  Hypothesis TLet_case : forall t1 t2, P t1 -> P t2 -> P (TLet t1 t2).
  Hypothesis TApp_case : forall def v, P (TApp def v).
  Hypothesis TSpawn_case : forall t, P t -> P (TSpawn t).
  Hypothesis TNew_case : P TNew.
  Hypothesis TSend_case : forall v1 m v2, P (TSend v1 m v2).
  Hypothesis TGuard_case : forall v e gs, Forall PG gs -> P (TGuard v e gs).
  Hypothesis GFail_case : PG GFail.
  Hypothesis GFree_case : forall t, P t -> PG (GFree t).
  Hypothesis GReceive_case : forall m t, P t -> PG (GReceive m t).

  Definition Term_ind3 (t : Term) : P t :=
    fix F (t : Term) : P t :=
      match t return (P t) with
      | TValue v => TValue_case v
      | TLet t1 t2 => TLet_case t1 t2 (F t1) (F t2)
      | TApp def v => TApp_case def v
      | TSpawn t => TSpawn_case t (F t)
      | TNew => TNew_case
      | TSend v1 m v2 => TSend_case v1 m v2
      | TGuard v e gs => TGuard_case v e gs
          ((fix Guards_ind (gs : list Guard) : (Forall PG gs) :=
            match gs with
            | nil => Forall_nil PG
            | g :: gs' => Forall_cons _ (FG g) (Guards_ind gs')
            end
            ) gs)
      end
    with FG (g : Guard) : PG g :=
      match g return (PG g) with
      | GFail => GFail_case
      | GFree t => GFree_case t (F t)
      | GReceive m t => GReceive_case m t (F t)
      end
    for F t.

End term_ind.


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
  | ValueVar x => x :: nil
  | _ => nil
  end.

Fixpoint FV (t : Term) : set nat :=
  match t with
  | TValue v => FV_val v
  | TLet t1 t2  =>
      set_union Nat.eq_dec (FV t1) (downShift 1 (set_remove Nat.eq_dec 0 (FV t2)))
  | TApp _ v => FV_val v
  | TSpawn t1 => FV t1
  | TNew => nil
  | TSend v m value =>
      set_union Nat.eq_dec (FV_val v) (FV_val value)
  | TGuard v _ guards =>
      set_union Nat.eq_dec (FV_val v) (set_concat (map (fun v => FV_guard v) guards))
  end
with FV_guard (g : Guard) : list nat :=
  match g with
  | GFail => nil
  | GFree t1 => FV t1
  | GReceive m t1 =>
      (downShift (content_size m) (set_diff Nat.eq_dec (FV t1) (seq 0 ((content_size m)))))
  end.

End free_var_def.
