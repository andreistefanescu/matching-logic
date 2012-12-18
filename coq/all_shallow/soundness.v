Add LoadPath "../ml_proof".

Require Import reduction.

Require Import proofsystem.
Set Implicit Arguments.

Require Import Setoid.
Require Import Relation_Definitions.

Section domain.
Variable cfg : Set.

(* step according to a system *)
Inductive ts (S : system cfg) : cfg -> cfg -> Prop :=
  | ts_step : forall gamma gamma' env phi phi',
    S env phi phi' ->
    (exists rho, phi gamma rho /\ phi' gamma' rho) ->
    ts S gamma gamma'.

Section FixBaseSystem.

(* underlying transition relation *)
Variable SF : cfg -> cfg -> Prop.

Inductive all_reach (env : Type) (phi : formula cfg env) (rho : env) (gamma : cfg) : bool -> Prop :=
  | reach_here : phi gamma rho -> all_reach phi rho gamma false
  | reach_later : forall strict,
                    (exists gamma', SF gamma gamma') ->
                  (forall gamma', SF gamma gamma' -> all_reach phi rho gamma' false) ->
                  all_reach phi rho gamma strict.

Lemma all_reach_unstrict env phi rho gamma strict :
  @all_reach env phi rho gamma true ->
  @all_reach env phi rho gamma strict.
Proof.
inversion 1; eauto using all_reach.
Qed.


Section AllReachAdequacy.
(* Various proofs to check that all_reach is reasonable *)
Inductive trace (start : cfg) : cfg -> Set :=
  | trace_done : trace start start
  | trace_step : forall next last, SF start next -> trace next last -> trace start last.
Inductive trace_hits (P : cfg -> Prop) : forall {s1 s2 : cfg}, trace s1 s2 -> Prop :=
  | hits_here : forall first last (t : trace first last), P first -> trace_hits P t
  | hits_later : forall first next last (step : SF first next) (t : trace next last),
                   trace_hits P t -> trace_hits P (trace_step step t).

Lemma all_reach_reaches :
  forall env (phi : formula cfg env) (rho : env) (gamma gamma' : cfg)
         (t : trace gamma gamma') strict,
    all_reach phi rho gamma strict ->
    trace_hits (fun cfg => phi cfg rho) t
               \/ all_reach phi rho gamma' false.
Proof.
induction t; intros.    
right. destruct strict;[apply all_reach_unstrict|];assumption.
destruct H.
left. apply hits_here; assumption.
specialize (H0 _ s).
specialize (IHt _ H0).
clear -IHt.
destruct IHt;[left|right;assumption].
auto using hits_later.
Qed.

Lemma all_reach_path :
  forall env (phi : formula cfg env) (rho : env) (gamma : cfg) strict,
    all_reach phi rho gamma strict ->
    exists gamma', clos SF strict gamma gamma' /\ phi gamma' rho.
induction 1.
exists gamma. split;[auto using clos_refl|assumption].
destruct H.
clear H0.
specialize (H1 x H).
destruct H1.
exists x0.
destruct H0.
split;[|assumption].
assert (clos SF true gamma x0) by eauto using clos_step, clos_trans_lt.
destruct strict;[|apply clos_unstrict];assumption.
Qed.
End AllReachAdequacy.

(* at points under gamma, the rule holds semantically *)
Definition gamma_entails parent strict env
  (phi phi' : formula cfg env) :=
  forall rho gamma,
    clos SF false parent gamma ->
    phi gamma rho ->
    all_reach phi' rho gamma strict.

Lemma gamma_entails_fwd :
  forall (gamma gamma' : cfg),
    clos SF false gamma gamma' ->
    forall strict env (phi phi' : formula cfg env),
      gamma_entails gamma strict phi phi'->
      gamma_entails gamma' strict phi phi'.
Proof.
  unfold gamma_entails. intros. eauto using clos_trans.
Qed.

Definition gamma_entails_system parent strict (S : system cfg) :=
  forall env (phi phi' : formula cfg env), S env phi phi' ->
    gamma_entails parent strict phi phi'.

Lemma gamma_system_fwd : forall gamma gamma' strict S,
  clos SF false gamma gamma' ->
  gamma_entails_system gamma strict S ->
  gamma_entails_system gamma' strict S.
Proof.
  unfold gamma_entails_system.
  intuition.
  eauto using gamma_entails_fwd.
Qed.

Lemma all_reach_impl :
  forall env (phi phi' : formula cfg env) rho gamma strict,
    (forall gamma rho, phi gamma rho -> phi' gamma rho) ->
    all_reach phi rho gamma strict ->
    all_reach phi' rho gamma strict.
Proof.
intros.
induction H0; eauto using all_reach.
Qed.

Lemma gamma_system_cons : forall gamma S env
  (phi phi' : formula cfg env),
  gamma_entails_system gamma true S ->
  gamma_entails gamma true phi phi' ->
   gamma_entails_system gamma true (cons_system cfg env phi phi' S).
Proof.
  intros. intro env0. intros.
  destruct H1.
  (* from system *)
  solve[auto].
  (* new rule *)
  destruct H1 as [Heq [Hphi Hphi']].
  subst env0.
  unfold eq_rect_r in * |-; simpl in * |-.
  clear -H0 Hphi Hphi'.
  intro rho; intros.
  rewrite <- Hphi in H1.
  specialize (H0 rho gamma0 H H1).
  clear -Hphi' H0.
  revert H0; apply all_reach_impl.
  apply Hphi'.
Qed.

Lemma gamma_entails_unstrict :
  forall gamma strict env (phi phi' : formula cfg env),
  gamma_entails gamma true phi phi' ->
  gamma_entails gamma strict phi phi'.
Proof.
  unfold gamma_entails.
  firstorder.
  specialize (H rho gamma0 H0 H1).
  inversion H.
  constructor.
  assumption.
  assumption.
Qed.

Lemma all_step_trans
  env
  (phi' phi'' : formula cfg env)
  (rho : env)
  (gamma' : cfg) :
   gamma_entails gamma' false phi' phi'' ->
   all_reach phi' rho gamma' false -> all_reach phi'' rho gamma' false.
Proof.
induction 2.
apply H; solve[auto using clos_refl].
constructor.
assumption.

intros.
apply H2.
assumption.
destruct strict.
apply gamma_entails_unstrict.
revert H.
apply gamma_entails_fwd.
auto using clos_step.
revert H.
apply gamma_entails_fwd.
auto using clos_step.
Qed.

Lemma gamma_entails_trans :
  forall gamma env (phi phi' phi'' : formula cfg env),
    gamma_entails gamma true phi phi' ->
    (forall gamma',
      clos SF true gamma gamma' ->
      gamma_entails gamma' false phi' phi'') ->
    gamma_entails gamma true phi phi''.
Proof.
  unfold gamma_entails.
  intros.
  specialize (H rho gamma0 H1 H2).
  destruct H.
  eapply H0.
  eassumption. constructor.
  assumption.

  (* step case *)
  constructor.
  assumption.
  intros.
  specialize (H3 _ H4).
  revert H3.
  apply all_step_trans.
  unfold gamma_entails; intros.
  specialize (H0 gamma1).
  assert (clos SF strict gamma gamma1).
  assert (clos SF true gamma gamma1).
    clear -H1 H4 H3. apply (@clos_step _ SF) with (s := true) in H4.
  eauto using clos_trans_lt, clos_cons_rt.
    destruct strict;[|apply clos_unstrict];assumption.
  auto using clos_refl.
Qed.

Theorem soundness : forall strict S env phi phi',
  forall (proof : IS cfg SF S strict env phi phi'),
    forall gamma,
      terminates gamma SF ->
      gamma_entails_system gamma true S ->
      gamma_entails gamma strict phi phi'.

Proof.
  intros until phi'; intro proof.
  induction proof; intros gamma Hterm Hsystem.

(* refl *)
  intro gamma0; intros.
  solve [firstorder using clos_refl, all_reach].

(* step *)
  intro;intros.
  specialize (H rho gamma0 H1).
  destruct H.
  apply all_reach_unstrict.
  constructor.
  assumption.
  intros.
  specialize (H2 gamma' H3).
  constructor.
  assumption.

(* axiom *)
  apply gamma_entails_unstrict.
  apply gamma_entails_unstrict; solve[auto].

(* subst *)
  specialize (IHproof gamma Hterm Hsystem); clear -IHproof.
  unfold gamma_entails in * |- *. firstorder.
  specialize (IHproof (f rho) gamma0 H H0).
  revert IHproof. clear.
  solve[induction 1;constructor;(assumption || firstorder)].

(* trans *) 
  specialize (IHproof1 gamma Hterm Hsystem);
  specialize (IHproof2 gamma Hterm Hsystem);
  clear -IHproof1 IHproof2.
  unfold gamma_entails.
  intros.
  specialize (IHproof1 rho gamma0 H H0).
  destruct IHproof1.
  apply IHproof2; assumption.
  (* if it took a step, stuff *)
  constructor.
  assumption.
  intros.
  specialize (H2 gamma' H3).
  assert (clos SF false gamma gamma') by (eauto using clos).
  apply (gamma_entails_fwd H4) in IHproof2.
  revert IHproof2 H2; clear.
  solve[apply all_step_trans].

(* ps_case *)
  solve[firstorder].

(* ps_lf *)
  specialize (IHproof gamma Hterm Hsystem).
  revert IHproof; clear.
  intro; intro; intros.
  destruct H0.
  specialize (IHproof rho gamma0 H H0).
  clear -IHproof H1.
  induction IHproof;constructor;solve[auto].

(* ps_conseq *)
  specialize (IHproof gamma Hterm Hsystem).
  intros rho gamma0; intros.
  apply H in H2.
  specialize (IHproof rho gamma0 H1 H2).
  revert IHproof.
  apply all_reach_impl.
  assumption.

(* ps_abstr *)
  specialize (IHproof gamma Hterm Hsystem).
  intro; intros.
  destruct H0.
  specialize (IHproof (rho , x) gamma0 H H0).
  clear -IHproof.
  induction IHproof;constructor;assumption.

(* ps_circ *)
  specialize (IHproof1 gamma Hterm Hsystem).

  assert (forall gamma2,
    clos SF true gamma gamma2 ->
    gamma_entails gamma2 true phi phi' ->
    gamma_entails gamma2 false phi'' phi').
  intros.
  apply IHproof2;[solve[eauto using terminates_fwd]|].
  apply gamma_system_cons;[|assumption].
  clear -Hsystem H.
  unfold gamma_entails_system.
  intros. specialize (Hsystem env phi phi' H0).
  eauto using gamma_entails_fwd, clos_unstrict.

  clear IHproof2.
  rename H into IHproof2.

  cut (gamma_entails gamma true phi phi').
  apply gamma_entails_unstrict.

  apply terminates_trans in Hterm.
  revert Hterm. induction 1.

  eapply gamma_entails_trans;[eassumption|].
  intros.
  apply IHproof2;[assumption|].

  apply H0;
    eauto using gamma_entails_fwd, gamma_system_fwd,
      clos_unstrict, clos_trans.
Qed.

Definition empty_system : system cfg := fun env phi phi' => False.
Lemma empty_system_vacuous : forall gamma,
  gamma_entails_system gamma true empty_system.
unfold gamma_entails_system; simpl; intros.
destruct H.
Qed.

Theorem simple_soundness : forall strict env phi phi',
  IS cfg SF empty_system strict env phi phi' ->
  forall gamma : cfg, terminates gamma SF ->
  forall rho, phi gamma rho -> all_reach phi' rho gamma strict.
intros.
eapply soundness; eauto using empty_system_vacuous, clos_refl.
Qed.

End FixBaseSystem.
End domain.