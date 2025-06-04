

Inductive Fin : nat -> Type :=
  | z : forall n, Fin (S n)
  | s : forall n, Fin n -> Fin (S n).

Arguments s {_} _.

Fixpoint to_nat {n} (f : Fin n) : nat :=
  match f with
  | z _ => 0
  | s i => S (to_nat i)
  end.

Fixpoint from_nat (n : nat) : Fin (S n) :=
  match n with
  | 0 => z _
  | S n => s (from_nat n)
  end.

Definition greater_0 {n} (f : Fin n) :=
  match f with
  | z _ => False
  | _ => True
  end.

(** A variable is just a natural number bounded by some number n *)
Definition Name n := Fin n.

Inductive DepGraph : Type :=
  | DepGraph_Empty : DepGraph
  | DepGraph_Edge : forall n, Fin n -> Fin n -> DepGraph
  | DepGraph_Union : DepGraph -> DepGraph -> DepGraph
  | DepGraph_Restr : DepGraph -> DepGraph.

Arguments DepGraph_Edge {_} _ _.

Inductive DepGraph_Trans {n} (u v : Fin n) : DepGraph -> DepGraph -> Prop :=
  | G_Axiom_1 : DepGraph_Trans u v (DepGraph_Edge u v) DepGraph_Empty
  | G_Axiom_2 : DepGraph_Trans u v (DepGraph_Edge v u) DepGraph_Empty
  | G_Left : forall G1 G2 G1',
      DepGraph_Trans u v G1 G1' ->
      DepGraph_Trans u v (DepGraph_Union G1 G2) (DepGraph_Union G1' G2)
  | G_Right : forall G1 G2 G2',
      DepGraph_Trans u v G2 G2' ->
      DepGraph_Trans u v (DepGraph_Union G1 G2) (DepGraph_Union G1 G2')
  | G_Restr : forall (G1 G2 : DepGraph),
      ~ u = (z 0) ->
      (*~ v = (z 0) ->*)
      DepGraph_Trans u v G1 G2 ->
      DepGraph_Trans u v (DepGraph_Restr G1) (DepGraph_Restr G2).
