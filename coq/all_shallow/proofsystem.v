Section domain.
Variable cfg : Set.

Definition formula env : Type := env -> cfg -> Prop.
Definition stateless env : Type := env -> Prop.
(* Definition rule := { env : Type & formula env & formula env }. *)
Definition system := forall env,
  formula env -> formula env -> Prop.

Definition in_opt_system (S : option system) env (phi phi' : formula env) : Prop :=
  match S with
    | None => False
    | Some sys => sys env phi phi'
  end.

Definition cons_system env (phi phi' : formula env) (S : system) : system :=
  fun env0 X X0 =>
    S env0 X X0 \/
    {H : env = env0 | phi = eq_rect_r _ X H /\ phi' = eq_rect_r _ X0 H}.

Definition cons_opt_system env (phi phi' : formula env) (S : option system) : option system :=
  Some (cons_system env phi phi' (in_opt_system S)).

Definition system_empty (S : option system) : Prop :=
  match S with
    | Some _ => False
    | None => True
  end.

Definition union_system (C : option system) (S : system) : system :=
  match C with
    | None => S
    | Some S1 =>
      fun env0 X X0 => S1 env0 X X0 \/ S env0 X X0
  end.
  
(* accepts a rule if all instances come from the relation *)
Definition system_of_relation (R : cfg -> cfg -> Prop) : system :=
  fun env phi phi' =>
    forall (rho : env) gamma gamma',
      phi rho gamma -> phi' rho gamma' -> R gamma gamma'.

Section FixTransition.
Variable (S : cfg -> cfg -> Prop).

Inductive IS (C : option system) (A : system) : forall env,
  formula env -> formula env -> Prop :=
  | is_refl : forall env phi, system_empty C -> IS C A env phi phi
  | is_step : forall env (phi phi' : formula env),
                (forall e c, phi e c ->
                             (exists c2, S c c2) /\
                             (forall c2, S c c2 -> phi' e c2)) ->
                 IS C A env phi phi'
  | is_axiom : forall env phi phi',
                 A env phi phi' -> IS C A env phi phi'
  | is_subst : forall env env' f phi phi',
       IS C A env' phi phi' ->
       IS C A env (fun e g => phi (f e) g) (fun e g => phi' (f e) g)
  | is_trans : forall env phi phi' phi'',
       IS C A env phi phi' ->
       IS None (union_system C A) env phi' phi'' ->
       IS C A env phi phi''
  | is_case : forall env phi phi1 phi',
       IS C A env phi  phi' ->
       IS C A env phi1 phi' ->
       IS C A env (fun e g => phi e g \/ phi1 e g) phi'
  | is_lf : forall env phi phi' psi,
       IS C A env phi phi' ->
       IS C A env (fun e g => phi e g  /\ psi e)
                  (fun e g => phi' e g /\ psi e)
  | is_conseq : forall env 
       (phi1 phi1' phi2 phi2' : formula env),
       (forall e g, phi1 e g -> phi1' e g) ->
       (forall e g, phi2 e g -> phi2' e g) ->
       IS C A env phi1' phi2 ->
       IS C A env phi1 phi2'
(* use embedding projection pair -
   have env, env' bigger,
   env' phi (fun e' => phi' (project e'))
   env (fun e => exists e', extends e e' /\ phi e') phi'
  *)
  | is_abstr : forall env denx
       (phi : formula (env * denx)) (phi' : formula env),
       IS C A (env * denx) phi (fun rho_and_x g => phi' (fst rho_and_x) g) ->
       IS C A env (fun rho g => exists x, phi (rho , x) g) phi'
  | is_circ : forall env phi phi',
       IS (cons_opt_system env phi phi' C) A env phi phi' ->
       IS C A env phi phi'.
End FixTransition.

End domain.