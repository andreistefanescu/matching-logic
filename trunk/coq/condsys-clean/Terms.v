Module Type Terms.

  Parameter T : Set.
  Parameter IsVariable : T -> Prop.

  Definition Var : Set := { x : T & (IsVariable x) }.

  Parameter Substitution : Set.
  Parameter identity : Substitution.
  Parameter Apply : Substitution -> T -> T.

  Hypothesis identity_refl : forall t, (Apply identity t) = t.
  Parameter Update : Substitution -> Var -> T -> Substitution.

End Terms.
