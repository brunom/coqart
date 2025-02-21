Require Import Arith.

Record RatPlus : Set := mkRat
  {top : nat; bottom : nat; bottom_condition : bottom <> 0}.

Axiom
  eq_RatPlus :
    forall r r':RatPlus, top r * bottom r' = top r' * bottom r -> r = r'.

Goal False.
cut (1 <> 0).
cut (2 <> 0).
intros H2 H1.
discriminate (eq_RatPlus (mkRat 0 1 H1) (mkRat 0 2 H2)).
simpl.
trivial.
discriminate.
discriminate.
Qed.