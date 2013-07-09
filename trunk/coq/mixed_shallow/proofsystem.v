Set Implicit Arguments.

Section domain.
Variable cfg : Set.

Definition formula env : Type := env -> cfg -> Prop.
Definition stateless env : Type := env -> Prop.
(* Definition rule := { env : Type & formula env & formula env }. *)

Inductive flag : Set := all_path | ex_path.
Inductive rule (env : Type) : Type :=
  Rule (f:flag) (phi phi':formula env).

Definition system := forall env, rule env -> Prop.

Definition in_opt_system (S : option system) : system :=
  match S with
    | None => fun _ _ => False
    | Some sys => sys
  end.

Definition empty_system : system := fun _ _ => False.

Definition cons_system env (r : rule env) (S : system) : system :=
  fun env0 r' => S env0 r' \/ {H : env = env0 | r = eq_rect_r _ r' H}.

Definition cons_opt_system env (r : rule env) (S : option system) : option system :=
  Some (cons_system r (in_opt_system S)).

Definition system_opt (C : option system) : system :=
  match C with
    | None => empty_system
    | Some s => s
  end.

Definition system_empty (S : option system) : Prop :=
  match S with
    | Some _ => False
    | None => True
  end.

Definition union_system (S1 S2 : system) : system :=
  fun env r => S1 env r \/ S2 env r.
  
(* accepts a rule if valid in the system *)
(*
Definition system_of_relation (R : cfg -> cfg -> Prop) : system :=
*)

Section FixTransition.
Variable (S : cfg -> cfg -> Prop).

Inductive IS (C : option system) (A : system) : forall env, rule env -> Prop :=
  | is_all_step : forall env (phi phi' : formula env),
                    (forall e c, phi e c ->
                                 (exists c2, S c c2) /\
                                 (forall c2, S c c2 -> phi' e c2)) ->
                    IS C A (Rule all_path phi phi')
  | is_ex_step : forall env (phi phi' : formula env),
                   (forall e c, phi e c -> exists c2, S c c2 /\ phi' e c2) ->
                   IS C A (Rule ex_path phi phi')
  | is_axiom : forall env r, A env r -> IS C A r
  | is_refl : forall env f phi, system_empty C -> IS C A (@Rule env f phi phi)
  | is_trans : forall env f (phi phi' phi'' : formula env),
       IS C A (Rule f phi phi') ->
       IS None (union_system A (system_opt C)) (Rule f phi' phi'') ->
       IS C A (Rule f phi phi'')
  | is_conseq : forall f env 
       (phi1 phi1' phi2 phi2' : formula env),
       (forall e g, phi1 e g -> phi1' e g) ->
       (forall e g, phi2 e g -> phi2' e g) ->
       IS C A (Rule f phi1' phi2) ->
       IS C A (Rule f phi1 phi2')
  | is_case : forall env f phi phi1 phi',
       IS C A (@Rule env f phi  phi') ->
       IS C A (Rule f phi1 phi') ->
       IS C A (Rule f (fun e g => phi e g \/ phi1 e g) phi')
(* use embedding projection pair -
   have env, env' bigger,
   env' phi (fun e' => phi' (project e'))
   env (fun e => exists e', extends e e' /\ phi e') phi'
  *)
  | is_abstr : forall f env denx
       (phi : formula (env * denx)) (phi' : formula env),
       IS C A (@Rule (env * denx) f phi (fun rho_and_x g => phi' (fst rho_and_x) g)) ->
       IS C A (Rule f (fun rho g => exists x, phi (rho , x) g) phi')
  | is_circ : forall env f phi phi',
       IS (cons_opt_system (Rule f phi phi') C) A (@Rule env f phi phi') ->
       IS C A (Rule f phi phi')
  | is_subst : forall env env' flg (f : env -> env') (phi phi' : formula env'),
       IS C A (Rule flg phi phi') ->
       IS C A (Rule flg (fun e g => phi (f e) g) (fun e g => phi' (f e) g))
  | is_lf : forall env f phi phi' psi,
       IS C A (@Rule env f phi phi') ->
       IS C A (Rule f (fun e g => phi e g  /\ psi e)
                      (fun e g => phi' e g /\ psi e)).

(*
Section StepGood.
Variable (Ssys : system).
Hypothesis (Ssys_welldef :
              forall env phi phi' e c1,
                (Ssys env phi phi' /\ phi e c1) ->
                exists c2, phi' e c2).
Hypothesis (Ssys_good :
              forall c1 c2, S c1 c2 <-> 
                            exists env phi phi' e,
              (Ssys env phi phi' /\ phi e c1 /\ phi' e c2)).

(* Check that the step rule is faithful compared to the
   paper proof as long as S is generated from
   a set of sell-defined reachability rules *)

Lemma s_prog :
  forall c,
    (exists c2, S c c2)
      <-> (exists env phi phi' e,
            Ssys env phi phi' /\ phi e c).
split. firstorder eauto.
intros.
destruct H as (env & phi & phi' & e & H).
specialize (@Ssys_welldef env phi phi' e c H).
destruct Ssys_welldef.
exists x.
apply Ssys_good.
firstorder eauto.
Qed.

Lemma s_succs :
  forall env1 (e : env1) c (phi_g : formula env1),
    ((forall c2, S c c2 -> phi_g e c2)
      <->
     (forall env phi phi',
       Ssys env phi phi' ->
       forall e2, phi e2 c ->
                  forall c2, phi' e2 c2 -> phi_g e c2)).
Proof.
intros.
split.
intros.
apply H.
apply Ssys_good.
firstorder eauto.

intros.
apply Ssys_good in H0.
destruct H0 as (env & phi & phi' & e2 & Hssys & Hphi & Hphi').
apply (H env phi phi' Hssys e2 Hphi c2 Hphi').
Qed.
End StepGood.
*)
End FixTransition.

End domain.
