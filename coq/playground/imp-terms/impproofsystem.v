Add LoadPath "../../ml_proof".

Require Import domains.
Require Import contexts.

Inductive IS :
  (cfg -> Prop) -> (cfg -> Prop) -> Prop :=
  | is_refl : forall phi, IS phi phi
  | is_axiom : forall (P Q : cfg -> Prop),
    (forall gamma, P gamma ->
      exists gamma', step gamma gamma' /\ Q gamma')
    -> IS P Q
    (* need some side conditions here? probably *)
  | is_subst : forall (P Q : cfg -> Prop) (rho : cfg -> cfg),
    IS P Q -> IS (fun c => P (rho c)) (fun c => Q (rho c))
  | is_trans : forall (P G Q : cfg -> Prop),
    IS P G -> IS G Q -> IS P Q
  | is_case : forall (P P' Q : cfg -> Prop),
    IS P Q -> IS P' Q -> IS (fun c => P c \/ P' c) Q
  | is_lf ?? (* how do we separate pure logic? *)