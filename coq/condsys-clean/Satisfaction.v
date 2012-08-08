Require Import Terms.
Require Import Model.
Require Import Patterns.

Module Type Satisfaction (Export Base : Terms)
  (Export BaseM : Model Base)
  (Export BaseP : Patterns Base).

  Parameter Satisfies : M -> Valuation -> Pattern -> Prop.

  Axiom SatApply : forall rho phi subst gamma,
    Satisfies gamma rho (ApplyF subst phi) <->
    Satisfies gamma (ApplyV subst rho) phi.

  Axiom structureless_sat : forall phi, structureless phi ->
    forall gamma gamma' rho,
      Satisfies gamma rho phi ->
      Satisfies gamma' rho phi.

  Axiom notFree_sat : forall x phi,
    notFree x phi ->
    forall gamma rho t,
      Satisfies gamma rho phi <->
      Satisfies gamma (UpdateV rho x t) phi.

  Definition ValidPattern phi :=
    forall gamma rho,
      Satisfies gamma rho phi.

  Definition StructurelessPattern phi :=
    forall rho,
      forall gamma gamma',
        Satisfies gamma rho phi <->
        Satisfies gamma' rho phi.

  Definition WeaklyWDPattern phi :=
    forall rho,
      exists gamma,
        Satisfies gamma rho phi.

  Definition WDPattern phi :=
    WeaklyWDPattern phi /\
    forall rho,
      forall gamma gamma',
        Satisfies gamma rho phi ->
        Satisfies gamma' rho phi ->
        gamma = gamma'.

(*  Axiom SatEquals : forall rho t t' gamma,
    value rho t = value rho t'
    <->
    Satisfies gamma rho (Equals t t').*)

  Axiom SatExists : forall rho x phi gamma,
    (exists t : M, Satisfies gamma (UpdateV rho x t) phi)
    <->
    Satisfies gamma rho (Exists x phi).

  Axiom SatAnd : forall rho phi phi' gamma,
    (Satisfies gamma rho phi /\ Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (And phi phi').

  Axiom SatOr : forall rho phi phi' gamma,
    (Satisfies gamma rho phi \/ Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (Or phi phi').

  Axiom SatImplies : forall rho phi phi' gamma,
    (Satisfies gamma rho phi -> Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (Implies phi phi').

(*  Axiom SatPattern : forall rho t gamma,
    (Some gamma = value rho t)
    <->
    Satisfies gamma rho (Pattern t).*)

End Satisfaction.
