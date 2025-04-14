(** Utility definitions *)

Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Forall3.

Variables A B C : Type.
Variable R : A -> B -> C -> Prop.

(** Predicate for stating that three lists are componentwise related
    Based on Forall2 from the stdlib.
*)
Inductive Forall3 : list A -> list B -> list C -> Prop :=
  | Forall3_nil : Forall3 nil nil nil
  | Forall3_cons : forall x y z l1 l2 l3,
    R x y z ->
    Forall3 l1 l2 l3 ->
    Forall3 (x :: l1) (y :: l2) (z :: l3).

Lemma Forall3_refl : Forall3 nil nil nil.
Proof. constructor. Qed.

End Forall3.
