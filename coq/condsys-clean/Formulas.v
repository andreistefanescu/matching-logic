Require Import Terms.

Module Type AbstractML (Export Base : Terms).

  Parameter Formula : Set.

  Parameter Equals : T -> T -> Formula.
  Parameter And : Formula -> Formula -> Formula.
  Parameter Or : Formula -> Formula -> Formula.
  Parameter Implies : Formula -> Formula -> Formula.
  Parameter Exists : Var -> Formula -> Formula.
  Parameter Pattern : T -> Formula.

  Parameter ApplyF : Substitution -> Formula -> Formula.

  Parameter notFree : Var -> Formula -> Prop.

  Parameter stateless : Formula -> Prop.

End Formulas.
