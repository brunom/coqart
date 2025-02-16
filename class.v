Definition peirce := forall P Q:Prop, ((P->Q)->P)->P.
Definition classic := forall P:Prop, ~~P -> P.
Definition excluded_middle := forall P:Prop, P\/~P.
Definition de_morgan_not_and_not := forall P Q:Prop, ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, (P->Q)->(~P\/Q).

Goal peirce -> classic.
intros Peirce P NegNeg. 
eapply Peirce.
intros Neg.
elim NegNeg.
exact Neg.
Qed.

Goal classic -> excluded_middle.
intros Classic P.
apply Classic.
intros Nor.
apply Nor.
right.
intros Pos.
apply Nor.
left.
apply Pos.
Qed.

Goal excluded_middle -> de_morgan_not_and_not.
intros excluded_middle P Q NegAndNeg.
elim (excluded_middle P); elim (excluded_middle Q); auto.
intros.
elim NegAndNeg.
split; auto.
Qed.

Goal de_morgan_not_and_not -> implies_to_or.
intros de_morgan_not_and_not P Q Then.
apply de_morgan_not_and_not.
intro And.
elim And.
auto.
Qed.


Goal implies_to_or -> peirce.
unfold implies_to_or.
intros implies_to_or P Q H.
absurd Q.
elim (implies_to_or P Q).
intros.
apply H.
intros.
elim H0.
auto.
auto.
absurd P.
admit.

Qed.
