Section domain.
Variable cfg : Set.

Definition formula env : Type := cfg -> env -> Prop.
Definition stateless env : Type := env -> Prop.
(* Definition rule := { env : Type & formula env & formula env }. *)
Definition system := forall env,
  formula env -> formula env -> Prop.

Definition cons_system env (phi phi' : formula env) (S : system) : system := fun env0 X X0 =>
  S env0 X X0 \/
  {H : env = env0 |
    (forall gamma rho,
      phi gamma rho <-> eq_rect_r _ X H gamma rho)
  /\ (forall gamma rho,
    phi' gamma rho <-> eq_rect_r _ X0 H gamma rho)}.

(* accepts a rule if all instances come from the relation *)
Definition system_of_relation (R : cfg -> cfg -> Prop) : system :=
  fun env phi phi' =>
    forall (rho : env) gamma gamma',
      phi gamma rho -> phi' gamma' rho -> R gamma gamma'.

Inductive IS (S : system) : forall (strict : bool) env,
  formula env -> formula env -> Prop :=
  | is_refl : forall env phi, IS S false env phi phi
  | is_axiom : forall strict env phi phi', S env phi phi' ->
                IS S strict env phi phi'
  | is_subst : forall strict env env' f phi phi',
       IS S strict env' phi phi' ->
       IS S strict env (fun g e => phi g (f e)) (fun g e => phi' g (f e))
  | is_trans : forall strict env phi phi' phi'',
       IS S strict env phi phi' ->
       IS S false env phi' phi'' ->
       IS S strict env phi phi''
  | is_case : forall strict env phi phi1 phi',
       IS S strict env phi  phi' ->
       IS S strict env phi1 phi' ->
       IS S strict env (fun e g => phi e g \/ phi1 e g) phi'
  | is_lf : forall strict env phi phi' psi,
       IS S strict env phi phi' ->
       IS S strict env (fun g e => phi g e  /\ psi e)
                       (fun g e => phi' g e /\ psi e)
  | is_conseq : forall strict env 
       (phi1 phi1' phi2 phi2' : formula env),
       (forall g e, phi1 g e -> phi1' g e) ->
       (forall g e, phi2 g e -> phi2' g e) ->
       IS S strict env phi1' phi2 ->
       IS S strict env phi1 phi2'
(* use embedding projection pair -
   have env, env' bigger,
   env' phi (fun e' => phi' (project e'))
   env (fun e => exists e', extends e e' /\ phi e') phi'
  *)
  | is_abstr : forall strict env denx
       (phi : formula (env * denx)) (phi' : formula env),
       IS S strict (env * denx) phi (fun g rho_and_x => phi' g (fst rho_and_x)) ->
       IS S strict env (fun g rho => exists x, phi g (rho , x)) phi'
  | is_circ : forall strict env phi phi' phi'',
       IS S true env phi phi'' ->
       IS (cons_system env phi phi' S) false env phi'' phi' ->
       IS S strict env phi phi'.

End domain.