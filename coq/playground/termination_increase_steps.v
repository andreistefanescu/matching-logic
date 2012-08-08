Module Termination.

Parameter T : Set.

Parameter R : T -> T -> Prop.

Fixpoint terminates (n : nat) (gamma : T) : Prop :=
  match n with
    | O => False
    | S n' =>
      forall gamma' : T,
        (R gamma gamma' -> terminates n' gamma')
  end.

Require Import CpdtTactics.

Theorem terminates_monotone : forall n gamma,
  terminates n gamma -> terminates (S n) gamma.
  induction n.
  inversion 1.
  intros.
  simpl.
  intros.
  simpl in H.
  specialize (H gamma' H0).
  specialize (IHn gamma' H).
  simpl in IHn.
  specialize (IHn gamma'0 H1).
  assumption.
Qed.

End Termination.
