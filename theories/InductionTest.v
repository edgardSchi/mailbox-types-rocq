From Stdlib Require Import Arith.

Type lt_wf_double_rect.
Print lt_wf_double_rect.

Goal forall a b, a + b = 0.
intros.
induction a, b using lt_wf_double_rect.
