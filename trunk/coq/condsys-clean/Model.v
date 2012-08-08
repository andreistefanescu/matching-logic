Require Import Terms.

Module Type Model (Export Base : Terms).

  Parameter M : Set.

  Parameter Valuation : Set.

  Parameter value : Valuation -> T -> option M.

  Parameter UpdateV : Valuation -> Var -> M -> Valuation.

  Parameter ApplyV : Substitution -> Valuation -> Valuation.

End Model.
