Require Import Terms.

Module Type Patterns (Export Base : Terms).

  Parameter Pattern : Set.

(*  Parameter Equals : T -> T -> Formula. *)
  Parameter And : Pattern -> Pattern -> Pattern.
  Parameter Or : Pattern -> Pattern -> Pattern.
  Parameter Implies : Pattern -> Pattern -> Pattern.
  Parameter Exists : Var -> Pattern -> Pattern.
(*  Parameter Pattern : T -> Pattern. *)

  Parameter ApplyF : Substitution -> Pattern -> Pattern.

  Parameter notFree : Var -> Pattern -> Prop.

  Parameter structureless : Pattern -> Prop.

End Patterns.
