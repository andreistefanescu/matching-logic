Require Import Arith.

Require Import matchingl.
Require Import matchinglreduction.
Require Import matchinglproofsystem.

Module MatchLPartialCorrectness(Base : ObjectLanguage).

Module MatchLProofSystemBase := MatchLProofSystem Base.
Export MatchLProofSystemBase.

Require Import Arith.

Proposition forall_in : forall T P l (e : T),
  List.In e l ->
  List.Forall P l ->
  P e.
Proof.
  induction 2; firstorder congruence.
Qed.

Hint Rewrite <- SatAnd : SatRewrite.
Hint Rewrite <- SatEquals : SatRewrite.
Hint Rewrite <- SatExists : SatRewrite.
Hint Rewrite <- SatImplies : SatRewrite.
Hint Rewrite <- SatOr : SatRewrite.

Ltac keep_first_conjunct H :=
  match type of H with
    ?P /\ ?Q => let name := fresh in assert (name: P) by (apply H); clear H; rename name into H
  end.

Definition gamma_entails parent strict s r :=
  forall gamma : M,
    clos s false parent gamma ->
    forall rho : Valuation,
      Satisfies gamma rho (fst r) ->
      exists gamma' : M, clos s strict gamma gamma' /\ Satisfies gamma' rho (snd r).

Lemma gamma_entails_fwd gamma gamma' strict s r :
  clos s false gamma gamma' ->
  gamma_entails gamma strict s r ->
  gamma_entails gamma' strict s r.
Proof.
  intros. intro gamma0;intros.
  destruct H0 with gamma0 rho.
  eauto using clos_trans.
  assumption.
  exists x. firstorder.
Qed.

Lemma entails_forall_gamma_entails : forall A strict phi phi',
  (forall gamma, terminates gamma A ->
    gamma_entails gamma strict A (phi,phi')) <->
  entails strict A (phi,phi').
Proof. 
  split.
  firstorder using clos.
  intros; intro gamma0; intros.
  eauto using terminates_fwd.
Qed.

Lemma gamma_entails_unstrict : forall gamma A strict r,
  gamma_entails gamma true A r ->
  gamma_entails gamma strict A r.
Proof.
  unfold gamma_entails.
  firstorder.
  destruct (H gamma0 H0 rho H1).
  exists x.
  intuition.
  destruct strict; auto using clos_unstrict.
Qed.

Definition gamma_entails_system parent strict s (R : System) :=
  forall r, R r -> gamma_entails parent strict s r.

Lemma entails_system_forall_gamma_entails_system :
  forall A strict A',
  (forall gamma, terminates gamma A ->
    gamma_entails_system gamma strict A A') ->
  entails_system strict A A'.
Proof.
  unfold gamma_entails_system, entails_system.
  intros.
  destruct r.
  apply entails_forall_gamma_entails.
  auto.
Qed.

Lemma gamma_entails_system_fwd gamma gamma' strict s R :
  clos s false gamma gamma' ->
  gamma_entails_system gamma strict s R ->
  gamma_entails_system gamma' strict s R.
Proof.
  intro. unfold gamma_entails_system. intro.
  eauto using gamma_entails_fwd.
Qed.

Section FixSystem.

(* A is the new system, for some strange reason *)
Hypothesis SF : (M -> M -> Prop).

Definition gamma_rule (gamma : M) strict (phi phi' : Formula) :=
  gamma_entails gamma strict SF (phi,phi').

Definition gamma_system (gamma : M) strict (A' : System) : Prop :=
  gamma_entails_system gamma strict SF A'.

Theorem lemma1 : forall strict A phi phi',
  forall (proof : PS strict A phi phi'),
    forall gamma,
      terminates gamma SF ->
      gamma_system gamma true A ->
      gamma_rule gamma strict phi phi'.
  intros strict A phi phi' proof.
  induction proof; intros gamma Hterm Hproper.

  (* ps_refl *)
  subst strict. intro;intros.
  exists gamma0. solve[firstorder using clos_refl].

  (* ps_axiom *)
  apply gamma_entails_unstrict; solve [auto].

  (* ps_subst *)
  specialize (IHproof gamma Hterm Hproper).
  clear -IHproof.
  unfold gamma_rule, gamma_entails.
  simpl; setoid_rewrite SatApply.
  solve[firstorder].

  (* ps_trans *)
  specialize (IHproof1 gamma Hterm Hproper).
  specialize (IHproof2 gamma Hterm Hproper).
  clear -IHproof1 IHproof2.
  unfold gamma_rule, gamma_entails.
  intros.
  destruct (IHproof1 gamma0 H rho H0) as [x [xtranz xsat]].
  assert (clos SF false gamma x) by
    (clear -H xtranz; destruct strict;
      eauto using clos,clos_unstrict).
  destruct (IHproof2 x H1 rho xsat) as [gamma'' [Htranz Hsat'']].
  exists gamma''.
  split;[apply clos_trans_lt with x|];assumption.

  (* ps_case *)
  intros n Himpl.
  specialize (IHproof1 gamma Hterm Hproper).
  specialize (IHproof2 gamma Hterm Hproper).
  intro rho.
  simpl. rewrite <- SatOr.
  solve[firstorder].

  (* ps_lf *)
  specialize (IHproof gamma Hterm Hproper).
  unfold gamma_rule, gamma_entails.
  simpl.
  setoid_rewrite <- SatAnd.
  intros. destruct H1.
  destruct (IHproof gamma0 H0 rho H1) as [gamma'' [Htranz Hsat]].
  exists gamma''.
  firstorder.
  eapply patternless_sat; eassumption.

  (* ps_conseq *)
  unfold Valid in H, H0.
  setoid_rewrite <- SatImplies in H.
  setoid_rewrite <- SatImplies in H0.
  intro; intros.
  specialize (IHproof gamma Hterm Hproper gamma0).
  apply H in H2.
  solve[firstorder].

  (* ps_abstr *)
  intro; intros.
  simpl in H1.
  rewrite <- SatExists in H1.
  destruct H1.
  destruct (IHproof gamma Hterm Hproper gamma0 H0 _ H1).
  exists x0.
  rewrite <- notFree_sat in H2; assumption.

  (* ps_circ *) 
  specialize (IHproof1 gamma Hterm Hproper).
  
  assert (forall gamma' : M, clos SF false gamma gamma' ->
    gamma_rule gamma' true phi phi' ->
    gamma_rule gamma' false phi'' phi') as IH2.
  intros; apply IHproof2; unfold gamma_system.
    eauto using terminates_fwd.
    intros r Hr.
    destruct Hr.
    subst r;assumption.

    eapply gamma_entails_system_fwd;eassumption.

  clear -IHproof1 IH2 Hterm.

  cut (gamma_rule gamma true phi phi').

  apply gamma_entails_unstrict.

  apply terminates_trans in Hterm.
  revert Hterm.
  remember (SF) as s.
  induction 1.
  clear H.
  subst s.

  assert (forall y : M,
    clos SF true x y ->
    gamma_rule y true phi phi').
  intros.
  specialize (H0 y H).
  apply H0.
  revert IHproof1; apply gamma_entails_fwd.
  apply clos_unstrict; assumption.
  intros.
  apply IH2.
  clear -H H1. apply clos_unstrict. exact (clos_cat H H1).
  assumption.

  assert (forall y : M,
    clos SF true x y ->
    gamma_rule y false phi'' phi').
  intros.
  apply IH2. apply clos_unstrict. assumption.
  apply H. assumption.

  clear -IHproof1 H1.
  intro gamma_phi; intros.
  specialize (IHproof1 gamma_phi H rho H0).
  destruct IHproof1 as [gamma_phi' [Hstep Hsat]].

  assert (clos SF true x gamma_phi').
    clear -Hstep H. exact (clos_cat H Hstep).
  destruct (H1 gamma_phi' H2) with gamma_phi' rho.
  apply clos_refl.
  assumption.

  exists x0.
  intuition.
  clear -Hstep H4. exact (clos_cat Hstep H4).
Qed.
End FixSystem.

Theorem partial_correctness : forall S A strict phi phi',
  entails_system true S A ->
  PS strict A phi phi' ->
  entails strict S (phi,phi').
Proof.
intros.
apply entails_forall_gamma_entails.
intros.
assert (gamma_system S gamma true A).
revert H; unfold entails_system, gamma_system, gamma_entails_system.
intros. specialize (H r H2).
unfold gamma_entails; intros.
apply H.
eauto using terminates_fwd.
assumption.

eapply lemma1;eassumption.
Qed.

Theorem system_correctness : forall S strict phi phi',
  wd_system S ->
  PS strict S phi phi' ->
  entails strict (ts S) (phi,phi').
Proof.
Abort.

End MatchLPartialCorrectness.
