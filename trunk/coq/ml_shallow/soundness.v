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

(* at points under gamma, the rule holds semantically *)
(* TODO: give global version that people care directly about *)
Definition gamma_entails parent strict env
  (phi phi' : formula cfg env) :=
  forall gamma : cfg,
    clos SF false parent gamma ->
    forall rho : env,
      phi gamma rho ->
      exists gamma' : cfg,
        clos SF strict gamma gamma'
        /\ phi' gamma' rho.

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

Lemma gamma_system_cons : forall gamma S env
  (phi phi' : formula cfg env),
  gamma_entails_system gamma true S ->
  gamma_entails gamma true phi phi' ->
   gamma_entails_system gamma true (cons_system cfg env phi phi' S).
Proof.
  intros. intro env0. intros.
  destruct H1.
  (* from system *)
  auto.
  (* new rule *)
  destruct H1 as [Heq [Hphi Hphi']].
  subst env0.
  unfold eq_rect_r in * |-; simpl in * |-.
  clear -H0 Hphi Hphi'.
  intro gamma'; intros.
  rewrite <- Hphi in H1.
  specialize (H0 gamma' H rho H1).
  setoid_rewrite Hphi' in H0.
  assumption.
Qed.

Lemma gamma_entails_unstrict :
  forall gamma strict env (phi phi' : formula cfg env),
  gamma_entails gamma true phi phi' ->
  gamma_entails gamma strict phi phi'.
Proof.
  unfold gamma_entails.
  firstorder.
  destruct (H gamma0 H0 rho H1).
  exists x.
  intuition.
  destruct strict; auto using clos_unstrict.
Qed.

Lemma gamma_entails_trans :
  forall gamma env (phi phi' phi'' : formula cfg env),
    gamma_entails gamma true phi phi' ->
    (forall gamma',
      clos SF true gamma gamma' ->
      gamma_entails gamma' false phi' phi'') ->
    gamma_entails gamma true phi phi''.
Proof.
  intros. intro gamma0; intros.
  specialize (H gamma0 H1 rho H2).
  destruct H as [gamma' [Hstep Hphi']].
  specialize (H0 gamma' (clos_cat H1 Hstep)
    gamma' (clos_refl _ _) rho Hphi').
  destruct H0 as [gamma'0 [Hstep' Hphi'']].
  exists gamma'0.
  split;[|assumption].
  eauto using clos_trans_lt.
Qed.

Theorem soundness : forall strict S env phi phi',
  forall (proof : IS cfg S strict env phi phi'),
    forall gamma,
      terminates gamma SF ->
      gamma_entails_system gamma true S ->
      gamma_entails gamma strict phi phi'.

Proof.
  intros strict S env phi phi' proof.
  induction proof; intros gamma Hterm Hsystem.

(* refl *)
  intro gamma0; intros;
  exists gamma0; solve[firstorder using clos_refl].

(* axiom *)
  apply gamma_entails_unstrict; solve[auto].

(* subst *)
  specialize (IHproof gamma Hterm Hsystem); clear -IHproof.
  solve[firstorder].

(* trans *) 
  specialize (IHproof1 gamma Hterm Hsystem);
  specialize (IHproof2 gamma Hterm Hsystem);
  clear -IHproof1 IHproof2.
  unfold gamma_entails.
  intros.
  specialize (IHproof1 gamma0 H rho H0).
  destruct IHproof1 as [x [xtranz xsat]].
  assert (clos SF false gamma x) by
     (clear -H xtranz; destruct strict;
      eauto using clos,clos_unstrict).
  specialize (IHproof2 x H1 rho xsat).
  destruct IHproof2 as [gamma'' [Htranz Hsat'']].
  exists gamma''.
  split;[apply clos_trans_lt with x|];assumption.

(* ps_case *)
  solve[firstorder].

(* ps_lf *)
  specialize (IHproof gamma Hterm Hsystem).
  solve[firstorder].

(* ps_conseq *)
  specialize (IHproof gamma Hterm Hsystem).
  intro gamma0; intros.
  specialize (IHproof gamma0).
  apply H in H2.
  solve[firstorder].

(* ps_abstr *)
  solve[firstorder].

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
End FixBaseSystem.
End domain.
