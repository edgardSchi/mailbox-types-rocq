(** Utility definitions *)

From Stdlib Require Import List.
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

Section MaybeUtils.

Variables A B : Type.
Variable f : A -> B.
Variable P : A -> Prop.

Definition is_Some (e : option A) : Prop :=
  match e with
  | None => False
  | Some _ => True
  end.

Definition f_maybe (e : option A) : option B :=
  match e with
  | None => None
  | Some e' => Some (f e')
  end.

Definition map_maybe (l : list (option A)) : list (option B) :=
  map f_maybe l.

Definition ForallMaybe (l : list (option A)) : Prop :=
  Forall
    (fun x => match x with
              | None => True
              | Some a => P a
              end
    )
    l.

End MaybeUtils.

Section function_comp.

(** Defining function composition *)
Definition funcomp {X Y Z} (g : Y -> Z) (f : X -> Y) :=
  fun x => g (f x).

(** Notation for forward function composition *)
Notation "f >> g" := (funcomp g f) (*fun x => g (f x)*) (at level 50).

Lemma funcomp_assoc : forall {A B C D} (f : A -> B) (g : B -> C) (h : C -> D),
  (f >> g) >> h = f >> (g >> h).
Proof. intros; reflexivity. Qed.

End function_comp.
