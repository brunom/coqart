Require Import Arith.

Record RatPlus : Set := mkRat
  {top : nat; bottom : nat; bottom_condition : bottom <> 0}.

Axiom
  eq_RatPlus :
    forall r r':RatPlus, top r * bottom r' = top r' * bottom r -> r = r'.

Goal False.
ediscriminate (eq_RatPlus (mkRat 0 1 _) (mkRat 0 2 _)).
simpl.
trivial.
Unshelve.
discriminate.
discriminate.
Qed.