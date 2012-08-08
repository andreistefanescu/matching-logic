Module MatchLProofSystem.

Require Import matchingl.
Import MatchL.
Require Import matchinglreduction.
Import MatchLReduction.

Require Import List.

Inductive PS (strict : bool) : System -> Formula -> Formula -> Prop :=
| ps_refl :
  strict = false ->
  forall phi : Formula, forall A : System,
  PS strict A phi phi
| ps_axiom :
  forall A : System, forall phi phi' : Formula,
  In (phi, phi') A ->
  PS strict A phi phi'
| ps_subst :
  forall A : System, forall phi phi' : Formula,
  PS strict A phi phi' ->
  forall rho : Valuation,
  PS strict A (ApplyF rho phi) (ApplyF rho phi')
| ps_trans :
  forall A : System, forall phi1 phi2 phi3 : Formula,
  PS strict A phi1 phi2 ->
  PS strict A phi2 phi3 ->
  PS strict A phi1 phi3
| ps_case :
  forall A : System, forall phi phi1 phi2 : Formula,
  PS strict A phi1 phi ->
  PS strict A phi2 phi ->
  PS strict A (Or phi1 phi2) phi
| ps_lf :
  forall A : System, forall phi phi' psi : Formula,
  PS strict A phi phi' ->
  patternless psi ->
  PS strict A (And phi psi) (And phi' psi)
| ps_conseq : 
  forall A : System, forall phi1 phi1' phi2 phi2' : Formula,
  Valid (Implies phi1 phi1') ->
  PS strict A phi1' phi2' ->
  Valid (Implies phi2' phi2) ->
  PS strict A phi1 phi2
| ps_abstr :
  forall A : System, forall phi phi' : Formula, forall X : Var,
  PS strict A phi phi' ->
  notFree X phi' ->
  PS strict A (MatchL.Exists X phi) phi'
| ps_circ :
  forall A : System, forall phi phi' phi'' : Formula,
  PS true A phi phi'' ->
  PS strict (cons (phi, phi') A) phi'' phi' ->
  PS strict A phi phi'.

Definition PS29 := PS true.

Definition PS19 := PS false.

End MatchLProofSystem.
