Section fix_syntax.

Variable domain : Set.
Variable env : Set.
Notation formula := (domain -> env -> Prop).
Notation patternless := (env -> Prop).

Notation system := (formula -> formula -> Prop).

Section fix_system.

Variable SF : system.

Variable SF_wf : forall phi phi', SF phi phi' ->
  forall gamma rho,
    phi gamma rho -> exists gamma', phi' gamma' rho.

Definition ts : domain -> domain -> Prop :=
  fun gamma gamma' => exists phi, exists phi',
    SF phi phi' /\ exists rho, phi gamma rho /\ phi' gamma' rho.

CoInductive reach : domain -> formula -> Prop :=
  | done : forall (gamma : domain) (phi : formula),
      (exists rho, phi gamma rho) -> reach gamma phi
  | step : forall gamma gamma' phi,
      ts gamma gamma' -> reach gamma' phi -> reach gamma phi.

Definition lift (psi : patternless) : formula := fun _ => psi.

Definition and (phi phi' : formula) : formula :=
  fun gamma rho => phi gamma rho /\ phi' gamma rho.
Definition or (phi phi' : formula) : formula :=
  fun gamma rho => phi gamma rho \/ phi' gamma rho.
Definition implies (phi phi' : formula) : formula :=
  fun gamma rho => phi gamma rho -> phi' gamma rho.

Definition Valid (phi : formula) : Prop :=
  forall gamma rho, phi gamma rho.

Section IPS.
  Variable CPS : system.

  Inductive IPS : system :=
  | ps_axiom : forall (phi phi' : formula) (psi : patternless),
    SF phi phi' -> IPS (and phi (lift psi)) (and phi' (lift psi))
  | ps_trans : forall (phi phi' phi'' : formula),
      IPS phi phi' -> CPS phi' phi'' -> IPS phi phi''
  | ps_conseq : forall (phi phi' phi2 phi2' : formula),
    Valid (implies phi phi') ->
    IPS phi' phi2 ->
    Valid (implies phi2 phi2') ->
    IPS phi phi2'
  | ps_case : forall (phi phi1 phi' : formula),
    IPS phi phi' -> IPS phi1 phi' -> IPS (or phi phi1) phi'
  .
  (* toss in abs for quantifiers? *)
End IPS.

CoInductive CPS : system :=
| ps_refl : forall phi phi',
  Valid (implies phi phi') -> CPS phi phi'
| ps_release : forall phi phi', IPS CPS phi phi' -> CPS phi phi'
.

Lemma cps_conseq : forall (phi phi' phi2 phi2' : formula),
    Valid (implies phi phi') ->
    CPS phi' phi2 ->
    Valid (implies phi2 phi2') ->
    CPS phi phi2'.
Proof.
  destruct 2.
  intro. apply ps_refl.
  unfold Valid, implies in * |- *.
  firstorder.

  intro. apply ps_release.
  eauto using ps_conseq.
Qed.

Lemma cps_trans : forall (phi phi' phi'' : formula),
  CPS phi phi' -> CPS phi' phi'' -> CPS phi phi''.
Proof.
  destruct 1.

  (* If it was just a validity step, use weakening *)
  assert (Valid (implies phi'' phi'')) by firstorder.
  eauto using cps_conseq.

  (* otherwise it's a wrapped IPS, and we can build
     a wrapped ps_trans *)
  intro. apply ps_release.
  eauto using ps_trans.
Qed.

Lemma istep : forall phi phi',
  IPS CPS phi phi' ->
  forall gamma rho,
    phi gamma rho ->
    exists phi2, exists gamma2,
      ts gamma gamma2 /\ phi2 gamma2 rho /\ CPS phi2 phi'.
Proof.
induction 1; intros.

(* axiom *)
exists (and phi' (lift psi)).
destruct (SF_wf _ _ H _ _ (proj1 H0)).
exists x.
firstorder.
apply ps_refl.
clear; firstorder.

(* trans *)
specialize (IHIPS gamma rho H1).
destruct IHIPS as [phi2 [gamma2 [Hts [Hsat HCPS]]]].
exists phi2. exists gamma2.
intuition.
eauto using cps_trans.

(* conseq *)
specialize (H _ _ H2).
specialize (IHIPS _ _ H).
destruct IHIPS as [phiMid [x [Hts [Hsat Hcps]]]].
exists phiMid. exists x.
intuition.
assert (Valid (implies phiMid phiMid)) by (clear;firstorder).
eauto using cps_conseq.

(* case *)
destruct H1;[apply IHIPS1|apply IHIPS2]; assumption.
Qed.

Lemma sound : forall phi phi', CPS phi phi' ->
  forall gamma rho, phi gamma rho -> reach gamma phi'.
Proof.
cofix.
destruct 1.
clear sound.
intros. apply done. exists rho. firstorder.

intros.
pose proof (istep _ _ H gamma rho H0).
destruct H1 as [phi2 [gamma2 [Hts [Hsat HCPS]]]].
apply step with gamma2.
assumption.
apply sound with (phi:=phi2)(rho:=rho);assumption.
Qed.

End fix_system.
End fix_syntax.

(* Now this should be connected to the more syntactic circulariy *)
Notation domain := nat.
Notation env := nat.
Notation formula := (domain -> env -> Prop).
Notation patternless := (env -> Prop).
Notation system := (formula -> formula -> Prop).

Inductive dec_sys : system :=
  dec_step : dec_sys
  (fun gamma n => gamma = S n)
  (fun gamma n => gamma = n).

Lemma reduces : CPS nat nat dec_sys
  (fun gamma n => gamma = n)
  (fun gamma n => gamma = 0).
Proof.
  apply ps_release.
  apply ps_conseq with
    (phi' :=
      or _ _ (fun gamma n => exists m, n = S m /\ gamma = n)
         (fun gamma n => n = 0 /\ gamma = n))
    (phi2 := (fun gamma _ : env => gamma = 0)).

unfold Valid, implies, or.
intros. subst gamma. destruct rho; intuition eauto.

Focus 2. unfold Valid, implies. trivial.

apply ps_case.