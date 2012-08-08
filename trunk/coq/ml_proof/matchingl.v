Module Type Terms.
  Parameter T : Set.
  Parameter IsVariable : T -> Prop.
  Definition Var : Set := { x : T & (IsVariable x) }.
(*
  Parameter var_dec : forall x y : Var, {x = y} + {x <> y }. 
 *)
  Parameter Substitution : Set. (* Var -> T *)
  Parameter identity : Substitution.
  Parameter Apply : Substitution -> T -> T.
  Hypothesis identity_refl : forall t, (Apply identity t) = t.
  Parameter Update : Substitution -> Var -> T -> Substitution.
  Parameter notFreeT : Var -> T -> Prop.
End Terms.

Module Type Formulas (Export Base : Terms).

  Parameter Formula : Set.
  Parameter Equals : T -> T -> Formula.
  Parameter And  : Formula -> Formula -> Formula.
  Parameter Or  : Formula -> Formula -> Formula.
  Parameter Implies  : Formula -> Formula -> Formula.
  Parameter Exists : Var  -> Formula -> Formula.
  Parameter Pattern : T -> Formula.
  Parameter ApplyF : Substitution -> Formula -> Formula.

  Parameter notFree : Var -> Formula -> Prop.

  Parameter patternless : Formula -> Prop.
End Formulas.

Module Type Model(Export Base : Terms).
  
  Parameter M : Set.

  Parameter Valuation : Set. (* Var -> M *)
  Parameter value : Valuation -> T -> option M.
  Parameter UpdateV : Valuation -> Var -> M -> Valuation.

  Parameter Compose : Valuation -> Substitution -> Valuation.
End Model.

Definition SomeEqual A (l r : option A) : Prop :=
  match l, r with
  | Some lv, Some rv => lv = rv
  | _, _ => False
  end.

k
Module Type Satisfaction
  (Export Base : Terms)
  (Export BaseM : Model Base)
  (Export BaseF : Formulas Base).

  Parameter Satisfies : M -> Valuation -> Formula -> Prop.
  Axiom SatApply : forall rho f subst gamma,
    Satisfies gamma rho (ApplyF subst f) <->
    Satisfies gamma (Compose rho subst) f.

  Axiom patternless_sat : forall f, patternless f ->
    forall gamma gamma' rho,
      Satisfies gamma rho f -> Satisfies gamma' rho f.
  Axiom notFree_sat : forall x f,
    notFree x f ->
    forall gamma rho t,
      Satisfies gamma rho f
      <-> Satisfies gamma (UpdateV rho x t) f.

  Definition Valid phi :=
    forall gamma : M, forall rho : Valuation,
      Satisfies gamma rho phi.

  Axiom SatEquals : forall (rho : Valuation) (t t' : T) (gamma : M),
    SomeEqual _ (value rho t) (value rho t')
    <->
    Satisfies gamma rho (Equals t t').

  Axiom SatExists : forall (rho : Valuation) (x : Var) (phi : Formula) (gamma : M),
    (exists t : M, Satisfies gamma (UpdateV rho x t) phi)
    <->
    Satisfies gamma rho (Exists x phi).

  Axiom SatAnd : forall (rho : Valuation) (phi phi' : Formula) (gamma : M),
    (Satisfies gamma rho phi /\ Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (And phi phi').

  Axiom SatOr : forall (rho : Valuation) (phi phi' : Formula) (gamma : M),
    (Satisfies gamma rho phi \/ Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (Or phi phi').

  Axiom SatImplies : forall (rho : Valuation) (phi phi' : Formula) (gamma : M),
    (Satisfies gamma rho phi -> Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (Implies phi phi').

  Axiom SatPattern : forall (rho : Valuation) (t : T) (gamma : M),
    (Some gamma = value rho t)
    <->
    Satisfies gamma rho (Pattern t).
End Satisfaction.

Module Type ObjectLanguage.
  Declare Module Export Base : Terms.
  Declare Module Export BaseM : Model Base.
  Declare Module Export BaseF : Formulas Base.
  Declare Module Export BaseS : Satisfaction Base BaseM BaseF.
End ObjectLanguage.