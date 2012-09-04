Module ForallExists.

Require Import Classical.

Theorem forall_exists : forall D, forall P : D -> Prop,
  ~ (forall x : D, P x) <-> (exists x : D, ~ P x).
split.
intros.
Check Peirce.
apply Peirce.
intros.
exfalso.
apply H.
intros.
apply Peirce.
intros.
exfalso.
apply H0.
exists x.
assumption.
intros.
unfold not.
intros.
elim H.
intros.
assert (P x).
apply H0.
contradiction.
Qed.

Print forall_exists.

End ForallExists.
