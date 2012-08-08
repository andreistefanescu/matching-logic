Add LoadPath "../ml_proof".

Require Import reduction.

Require Import matchingl.
Require Import matchinglreduction.
Require Import matchinglproofsystem.
Require Import matchinglpartialcorrectness.

Require Import proofsystem.
Require Import soundness.

Require Import Setoid.
Require Import Relation_Definitions.

Set Implicit Arguments.

Module Adequacy(Import Base : ObjectLanguage).
(* explain how to derive a "system" from a "System" *)

Module Sound := MatchLPartialCorrectness Base.
Module Syntax := Sound.MatchLProofSystemBase.
Module Reduction := Syntax.Reduction.

Section FixReduction.

Variable SF : M -> M -> Prop.

(* use M as cfg *)
Definition formula_of_Formula (f : Formula)
  : formula M Valuation  :=
  fun gamma rho => Satisfies gamma rho f.

Lemma formula_of_Formula_faithful (f f' : Formula)
  : forall gamma strict,
    gamma_entails SF gamma strict
      (formula_of_Formula f)
      (formula_of_Formula f')
    <->
    Sound.gamma_entails gamma strict SF (f,f').
Proof.
  reflexivity.
Qed.

Definition system_of_System (S : Reduction.System) : system M.
unfold system.
refine (
  fun env phi phi' =>
    exists p, S p /\ {H : env = Valuation |
      _ /\ _}).
rewrite H in phi.
refine (forall (gamma:M) (rho:Valuation),
  phi gamma rho <-> formula_of_Formula (fst p) gamma rho).
rewrite H in phi'.
refine (forall (gamma:M) (rho:Valuation),
  phi' gamma rho <-> formula_of_Formula (snd p) gamma rho).
Defined.

Lemma lift_sys_rule (S : Reduction.System) (f f' : Formula) :
  S (f,f') ->
  system_of_System S (formula_of_Formula f) (formula_of_Formula f').
Proof.
  intro H.
  eexists; split;[eassumption|].
  apply exist with (x := eq_refl (Valuation:Type));
    split;reflexivity.
Qed.

Lemma system_of_System_faithful (S : Reduction.System) :
  forall gamma strict,
    Sound.gamma_entails_system gamma strict SF S
    <-> gamma_entails_system SF gamma strict (system_of_System S).
Proof.
  unfold gamma_entails_system, Sound.gamma_entails_system;
    split; intros.

  destruct H0 as [x [Sx [Heq [Hphi Hphi']]]].
  specialize (H x Sx).
  destruct x as [f f'].
  rewrite <- formula_of_Formula_faithful in H.
  subst env; simpl in Hphi, Hphi'.
  revert H; unfold gamma_entails.
  setoid_rewrite <- Hphi.
  setoid_rewrite <- Hphi'.
  solve[trivial].

  destruct r as [f f'].
  apply lift_sys_rule in H0.
  rewrite <- formula_of_Formula_faithful.
  solve[auto].
Qed.

Lemma sound_ts_faithful (S : Reduction.System) :
  forall gamma gamma',
    Reduction.ts S gamma gamma'
    <-> soundness.ts (system_of_System S) gamma gamma'.
Proof.
  unfold Reduction.ts; split.

  destruct 1 as [[f f'] [rho [Sr [Hgamma Hgamma']]]].
  solve [eauto using ts_step, lift_sys_rule].

  destruct 1.
  destruct H as [[f f'] [rho [Sr [Hgamma Hgamma']]]].
  subst env; simpl in Hgamma, Hgamma'.
  unfold formula_of_Formula in Hgamma, Hgamma'.
  exists (f,f').
  destruct H0 as [rho0].
  exists rho0.
  rewrite <- Hgamma, <- Hgamma'.
  intuition.
Qed.

Lemma adequate_iff_sys : forall (S : Reduction.System)
  strict (f f' : Formula),
  Syntax.PS strict S f f' ->
  forall (sys : system M)
    (Heqsys : (forall env phi phi',
      sys env phi phi' <-> system_of_System S phi phi')),
  IS M sys strict
  Valuation (formula_of_Formula f) (formula_of_Formula f').
Proof.
  induction 1; intros sys Heqsys;
  [repeat match goal with
  | [ H : forall (sys : system M), _ |- _] =>
       specialize (H _ Heqsys)
    end ..|].

  (* refl *)
  rewrite H; solve [apply is_refl].

  (* axiom *)
  apply is_axiom.
  unfold system_of_System.
  rewrite Heqsys.
  exists (phi, phi').
  split;[assumption|];
  refine (existT _ (eq_refl _) _);
  split;simpl;reflexivity.
     
  (* subst *)
  assert (IS M sys strict Valuation
    (fun gamma val => formula_of_Formula phi gamma (Compose val rho))
    (fun gamma val => formula_of_Formula phi' gamma (Compose val rho)))
   by (apply is_subst; solve[auto]).
  eapply is_conseq;[| |apply H0];
  clear;unfold formula_of_Formula;
    setoid_rewrite SatApply;solve[trivial].

  (* trans *)
  solve[eauto using IS].

  (* or *)
  eapply is_conseq;[| |eapply is_case with (1:=IHPS1) (2:=IHPS2)];
  unfold formula_of_Formula;
    try setoid_rewrite SatOr;solve[trivial].

  (* lf *)
  apply is_conseq
  with
    (phi1' := fun gamma rho =>
      (formula_of_Formula phi gamma rho /\
        (fun rho => forall gamma, formula_of_Formula psi gamma rho) rho))
    (phi2 := fun gamma rho =>
      (formula_of_Formula phi' gamma rho /\
        (fun rho => forall gamma, formula_of_Formula psi gamma rho) rho));[| |apply is_lf;assumption];
  (intros rho gamma;
  unfold formula_of_Formula;
  setoid_rewrite <- SatAnd;
  destruct 1;
  split;[assumption|solve[eauto using patternless_sat]]).

  (* conseq *)
  eapply is_conseq;[| |eapply IHPS].
  clear -H.
  intros gamma rho.
  specialize (H gamma rho).
  rewrite <- SatImplies in H.
  exact H.
  clear -H1.
  intros gamma rho.
  specialize (H1 gamma rho).
  rewrite <- SatImplies in H1.
  exact H1.

  (* abstraction ... *)
  apply is_conseq with
    (phi1' :=
      (fun gamma rho =>
        exists xv,
          (fun (p : Valuation * M) => let (rho, xv) := p in
          Satisfies gamma (UpdateV rho X xv) phi)
          (rho,xv)))
    (phi2 := formula_of_Formula phi');[
    unfold formula_of_Formula; setoid_rewrite <- SatExists;
      solve[trivial]|solve[trivial]|].

  change
    (fun (gamma : M) (rho : Valuation) =>
      exists xv : M, Satisfies gamma (UpdateV rho X xv) phi)
    with
      (fun gamma rho =>
        exists xv,
          (fun (p : Valuation * M) => let (rho, xv) := p in
          Satisfies gamma (UpdateV rho X xv) phi)
          (rho,xv)).
  apply is_abstr.

  apply is_conseq with
    (phi1' :=
      (fun (g : M) (p : Valuation * M) =>
        let (rho, xv) := p in Satisfies g (UpdateV rho X xv) phi))
    (phi2 := (fun (g : M) (p : Valuation * M) =>
      let (rho, xv) := p in Satisfies g (UpdateV rho X xv) phi'));
    [solve[trivial]|destruct e;apply notFree_sat;assumption|].

  apply is_conseq with
    (phi1' :=
      (fun (g : M) (e : Valuation * M) =>
        formula_of_Formula phi g
        ((fun (p : Valuation * M) => let (rho, xv) := p in (UpdateV rho X xv)) e)))
    (phi2 :=
      (fun (g : M) (e : Valuation * M) =>
        formula_of_Formula phi' g
        ((fun (p : Valuation * M) => let (rho, xv) := p in (UpdateV rho X xv)) e)));[destruct e;solve[trivial]..|].
  apply is_subst.
  assumption.
  
  (* circularity *)
  apply is_circ with
    (phi'' := formula_of_Formula phi'').
  auto.

  apply IHPS2.
  clear -Heqsys.
  intros env f f'.
  unfold cons_system.
  rewrite Heqsys.
  unfold system_of_System.
  clear.
  intuition.
  destruct H0 as [p [HAp Hexists]].
  exists p.
  split.
  right;assumption.
  assumption.
  exists (phi,phi').
  split.
  left. reflexivity.
  destruct H0 as [Heq [Hphi Hphi']].
  destruct Heq.
  apply exist with (x := eq_refl (Valuation:Type)).
  split.
  intros.
  simpl.
  rewrite Hphi.
  reflexivity.
  intros.
  simpl.
  rewrite Hphi'.
  reflexivity.

  destruct H as [p [Hca Hexist]].
  destruct Hca;[right|left].
  subst p.
  destruct Hexist as [Heq [Hphi Hphi']].
  subst.
  simpl in Hphi, Hphi'.
  apply exist with (x := eq_refl (Valuation:Type)).
  split; intros gamma rho.
  rewrite Hphi.
  reflexivity.
  rewrite Hphi'.
  reflexivity.

  exists p.
  split.
  assumption.
  assumption.
Qed.

Theorem adequate : forall (S : Reduction.System)
  strict (f f' : Formula),
  Syntax.PS strict S f f' ->
  IS M (system_of_System S) strict
  Valuation (formula_of_Formula f) (formula_of_Formula f').
Proof.
intros. apply (adequate_iff_sys H). reflexivity.
Qed.

End FixReduction.
End Adequacy.
   
