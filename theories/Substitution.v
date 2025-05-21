(** * Substitution *)

From MailboxTypes Require Export Environment.
From MailboxTypes Require Export Syntax.
From MailboxTypes Require Import Util.

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
  Definition id (v : nat) := v.

  (** Shifting is a renaming that increments a variable by one *)
  Definition shift := S.

  (** Extension extends a substitution sigma : nat -> Term with a new element *)
  Definition extend (v : nat) (xi : nat -> nat) :=
    fun n => match n with
             | 0 => v
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

  Fixpoint rename_Term (xi : nat -> nat) (t : Term) : Term :=
    match t with
    | TValue v => TValue (rename_Value xi v)
    | TLet t1 t2 => TLet (rename_Term xi t1) (rename_Term (lift_renaming xi) t2)
    | TApp def values => TApp def values
    | _ => t
    end.
  
  Definition up_Term_Term (sigma : nat -> Term) : nat -> Term :=
    extend () (funcomp () sigma).
  Definition subst_Term (sigma_term : nat -> Term) (t : Term) := t.
End subs_def.
