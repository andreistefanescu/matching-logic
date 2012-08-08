Module MatchLPartialCorrectness.

Require Import matchingl.
Import MatchL.
Require Import matchinglreduction.
Import MatchLReduction.
Require Import matchinglproofsystem.
Import MatchLProofSystem.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Arith.

Proposition forall_in : forall T P l (e : T),
  List.In e l ->
  List.Forall P l ->
  P e.
induction l.
intros. contradiction.
intros.
compute in H.
destruct H.
rewrite H in H0. inversion H0. assumption.
apply IHl.
apply H.
inversion H0.
assumption.
Qed.

Hint Rewrite <- SatNot : SatRewrite.
Hint Rewrite <- SatAnd : SatRewrite.
Hint Rewrite <- SatEquals : SatRewrite.
Hint Rewrite <- SatForall : SatRewrite.

Lemma patternless_formula : forall psi gamma gamma' rho,
  patternless psi ->
  (Satisfies gamma rho psi <->
  Satisfies gamma' rho psi).
intros. generalize dependent rho.
induction psi; intros; autorewrite with SatRewrite in *.
(* equals *)
simpl in H. tauto.
(* and *)
simpl in H. decompose [and] H.
specialize (IHpsi1 H0 rho).
specialize (IHpsi2 H1 rho).
tauto.
(* not *)
simpl in H. specialize (IHpsi H rho).
tauto.
(* forall *)
simpl in H. specialize (IHpsi H). firstorder.
(* pattern *)
simpl in H. contradiction.
Qed.

Lemma modus_ponens : forall phi phi' gamma rho,
  Valid (Implies phi phi') ->
  Satisfies gamma rho phi ->
  Satisfies gamma rho phi'.
intros.
unfold Implies in *.
unfold Or in *.
unfold Valid in *.
specialize (H gamma rho).
autorewrite with SatRewrite in *.
tauto.
Qed.

Ltac keep_first_conjunct H :=
  match type of H with
    ?P /\ ?Q => let name := fresh in assert (name: P) by (apply H); clear H; rename name into H
  end.

Lemma nterminates_gen_weaken : forall n m gamma A,
  nterminates_gen m gamma A ->
  m <= n ->
  nterminates_gen n gamma A.
  intros.
  induction H0.
  assumption.
  apply nterminates_monotone. assumption.
Qed.

Lemma nterminates_tranz : forall n gamma gamma' A,
  nterminates_gen n gamma A ->
  tranz (ts A) gamma gamma' ->
  exists n', (n' < n /\ nterminates_gen n' gamma' A).
intros.
generalize dependent n.
induction H0.
intros.
destruct n as [ | n' ].
inversion H0.
exists n'.
split.
constructor.
simpl in H0.
apply H0.
assumption.
intros.
specialize (IHclos_trans1 n H).
elim IHclos_trans1. intros n1 Htemp.
decompose [and] Htemp.
specialize (IHclos_trans2 n1 H1).
elim IHclos_trans2.
intros n' Htemp2.
decompose [and] Htemp2.
exists n'.
split.
eapply lt_trans.
apply H2.
assumption.
assumption.
Qed.

Lemma nproper_rule_gen_weaken : forall n m phi phi' A,
  nproper_rule_gen n A phi phi' ->
  m <= n ->
  nproper_rule_gen m A phi phi'.
  intros.
  unfold nproper_rule_gen in *.
  intros.
  specialize (H gamma).
  assert (nterminates_gen n gamma A). eapply nterminates_gen_weaken. apply H1. assumption.
  specialize (H H3 rho H2).
  exact H.
Qed.  

Lemma nproper_rule_weaken : forall n m phi phi',
  nproper_rule n phi phi' ->
  m <= n ->
  nproper_rule m phi phi'.
  unfold nproper_rule.
  intros. eapply nproper_rule_gen_weaken. apply H. assumption.
Qed.

Lemma nproper_system_weaken : forall n m A,
  nproper_system n A ->
  m <= n ->
  nproper_system m A.
intros.
unfold nproper_system in *.
unfold nproper_system_gen in *.
induction H.
constructor.
constructor. eapply nproper_rule_gen_weaken.
rewrite nproper_rule_gen_iff_nproper'_rule_gen.
apply H.
assumption.
apply IHForall.
Qed.

Lemma rule_transitivity : forall phi phi'' phi', forall m',
  nproper_rule (S m') phi phi'' ->
  nproper_rule m' phi'' phi' ->
  nproper_rule (S m') phi phi'.
  unfold nproper_rule in *. unfold nproper_rule_gen in *.
  intros phi phi'' phi' m' Hfirst Hsecond.
  intros gamma Hterm rho Hsat.
  specialize (Hfirst gamma Hterm rho Hsat).
  elim Hfirst. intros gamma' Htemp.
  assert (Htranz: tranz (ts SF) gamma gamma') by (apply Htemp).
  assert (Hsat2: Satisfies gamma' rho phi'') by (apply Htemp).
  clear Htemp.
  assert (Hterm2: exists n', n' < (S m') /\ nterminates_gen n' gamma' SF).
  eapply nterminates_tranz.
  apply Hterm.
  apply Htranz.
  elim Hterm2.
  intros n' Htemp.
  assert (Hterm' : nterminates_gen m' gamma' SF).
  eapply nterminates_gen_weaken.
  apply Htemp.
  unfold lt in Htemp.
  apply le_S_n.
  apply Htemp.
  specialize (Hsecond gamma' Hterm' rho Hsat2).
  elim Hsecond. intros gamma'' Htemp2.
  exists gamma''.
  split.
  eapply t_trans.
  apply Htranz.
  apply Htemp2.
  apply Htemp2.
Qed.

Lemma tranz_star : forall R gamma gamma',
  tranz R gamma gamma' ->
  forall gamma'', star R gamma' gamma'' ->
    tranz R gamma gamma''.
induction 2.
eapply t_trans.
apply H.
apply t_step.
apply H0.
assumption.
apply IHclos_refl_trans2.
apply IHclos_refl_trans1.
apply H.
Qed.

Lemma rule_transitivity' : forall phi phi'' phi', forall m',
  nproper_rule (S m') phi phi'' ->
  nsound_rule m' phi'' phi' ->
  nproper_rule (S m') phi phi'.
  unfold nproper_rule in *. unfold nproper_rule_gen in *.
  unfold nsound_rule in *. unfold nsound_rule_gen in *.
  intros phi phi'' phi' m' Hfirst Hsecond.
  intros gamma Hterm rho Hsat.
  specialize (Hfirst gamma Hterm rho Hsat).
  elim Hfirst. intros gamma' Htemp.
  assert (Htranz: tranz (ts SF) gamma gamma') by (apply Htemp).
  assert (Hsat2: Satisfies gamma' rho phi'') by (apply Htemp).
  clear Htemp.
  assert (Hterm2: exists n', n' < (S m') /\ nterminates_gen n' gamma' SF).
  eapply nterminates_tranz.
  apply Hterm.
  apply Htranz.
  elim Hterm2.
  intros n' Htemp.
  assert (Hterm' : nterminates_gen m' gamma' SF).
  eapply nterminates_gen_weaken.
  apply Htemp.
  unfold lt in Htemp.
  apply le_S_n.
  apply Htemp.
  specialize (Hsecond gamma' Hterm' rho Hsat2).
  elim Hsecond. intros gamma'' Htemp2.
  exists gamma''.
  split.
  eapply tranz_star.
  apply Htranz.
  apply Htemp2.
  apply Htemp2.
Qed.

Theorem lemma1 : forall A phi phi',
  forall (proof : PS29 A phi phi'),
    forall n,
      nproper_system n A ->
      nproper_rule n phi phi'.
  intros A phi phi' proof.
  unfold PS29 in proof.
  remember (true) as strict.
  induction proof as [
    strict Hstrict |
    strict |
    strict |
    strict |
    strict |
    strict |
    strict |
    strict |
    strict A ].
  
  (* ps_refl -- impossible *)
  rewrite Heqstrict in Hstrict.
  inversion Hstrict.
  
  (* ps_axiom *)
  intros n Himpl.
  rewrite nproper_rule_iff_nproper'_rule.
  eapply forall_in.
  eassumption.
  apply Himpl.

  (* ps_subst *)
  intros n Himpl.

  specialize (IHproof Heqstrict n Himpl).
  unfold nproper_rule in *.
  unfold nproper_rule_gen in *.
  intros.
  specialize (IHproof gamma H (Compose rho0 rho)).
  assert (Hnew: Satisfies gamma (Compose rho0 rho) phi).
  apply (SatApply gamma rho0 phi rho); assumption.
  specialize (IHproof Hnew).
  clear Hnew.
  elim IHproof.  
  intros gamma' Hconj.
  rewrite <- SatApply in Hconj.
  exists gamma'.
  apply Hconj.

  (* ps_trans *)
  intros n Himpl.

  specialize (IHproof1 Heqstrict n Himpl).
  specialize (IHproof2 Heqstrict n Himpl).
  unfold nproper_rule in *. unfold nproper_rule_gen in *.
  intros gamma Hterm rho Hsat.
  specialize (IHproof1 gamma Hterm rho Hsat).
  elim IHproof1. intros gamma'' Hand.
  decompose [and] Hand; clear Hand.
  specialize (IHproof2 gamma'').
  assert (Hn: nterminates_gen n gamma'' SF).
  eapply nterminates_gen_tranz. apply H. apply Hterm.
  specialize (IHproof2 Hn rho H0).
  elim IHproof2. intros gamma' Hand. decompose [and] Hand; clear Hand.
  exists gamma'.
  split.
  eapply t_trans. apply H. assumption.
  assumption.
  
  (* ps_case *)
  intros n Himpl.
  specialize (IHproof1 Heqstrict n Himpl).
  specialize (IHproof2 Heqstrict n Himpl).
  unfold nproper_rule in *. unfold nproper_rule_gen in *.
  intros gamma Hterm rho Hsat.
  unfold Or in Hsat.
  autorewrite with SatRewrite in Hsat.
  unfold not in Hsat.
  specialize (IHproof1 gamma Hterm rho).
  specialize (IHproof2 gamma Hterm rho).
  tauto.

  (* ps_lf *)
  intros n Himpl.
  specialize (IHproof Heqstrict n Himpl).
  unfold nproper_rule in *; unfold nproper_rule_gen in *.
  intros gamma Hterm rho Hsat. specialize (IHproof gamma Hterm rho).
  autorewrite with SatRewrite in *.
  decompose [and] Hsat; clear Hsat.
  specialize (IHproof H0).
  elim IHproof. intros x0 Htranz. decompose [and] Htranz.
  exists x0.
  split. assumption. autorewrite with SatRewrite in *.
  split. assumption. setoid_rewrite patternless_formula. apply H1. assumption.

  (* ps_conseq *)
  intros n Himpl.
  specialize (IHproof Heqstrict n Himpl).
  unfold nproper_rule in *; unfold nproper_rule_gen in *.
  intros gamma Hterm rho Hsat. specialize (IHproof gamma Hterm rho).
  assert (Satisfies gamma rho phi1').
  eapply modus_ponens. apply H. apply Hsat.
  specialize (IHproof H1).
  elim IHproof; intros gamma' Hand. decompose [and] Hand.
  exists gamma'. split. assumption.  
  eapply modus_ponens. apply H0. assumption.

  (* ps_abstr *)
  intros n Himpl.
  
  specialize (IHproof Heqstrict).
  unfold nproper_rule in *; unfold nproper_rule_gen in *.
  intros gamma Hterm rho Hsat.
  specialize (IHproof n Himpl gamma Hterm).
  rewrite SatExists in Hsat.
  destruct Hsat as [t Hsat'].
  specialize (IHproof (Update rho X t) Hsat').
  destruct IHproof as [gamma' [Htranz Hsatup]].
  exists gamma'.
  split.
  apply Htranz.
  rewrite (notFree_sat X phi' H).
  apply Hsatup.

  (* ps_circ *)
  
  intros n Himpl.
  rewrite Heqstrict in *; clear Heqstrict; clear strict; clear proof1; clear proof2.

  assert (forall m : nat, m <= n -> nproper_rule m phi phi').
  induction m as [ | m' ].
  (* m = 0 *)
  intros. unfold nproper_rule; unfold nproper_rule_gen.
  intros gamma Hterm rho Hsat. inversion Hterm.
  (* m = S m' *)
  intros Hcond.
  assert (Hmweak : m' <= n) by (apply le_Sn_le; assumption).
  specialize (IHm' Hmweak).
  specialize (IHproof1 (eq_refl true) n Himpl).
  specialize (IHproof2 (eq_refl true) m').
  assert (Hpropersystem : nproper_system m' ((phi, phi') :: A)%list).
  constructor.
  rewrite <- nproper_rule_gen_iff_nproper'_rule_gen.
  apply IHm'.
  eapply nproper_system_weaken.
  apply Himpl.
  assumption.
  specialize (IHproof2 Hpropersystem).
  assert (IHproof1' : nproper_rule (S m') phi phi'').
  eapply nproper_rule_weaken.
  apply IHproof1.
  assumption.
  eapply rule_transitivity.
  eassumption.
  assumption.
  apply H.
  apply le_refl.
Qed.  

Corollary corollary1 : forall A phi phi',
  proper_system A ->
  PS true A phi phi' ->
  proper_rule phi phi'.
intros.
unfold proper_system in H.
rewrite proper_system_forall_nproper_system in H.
unfold proper_rule.
rewrite proper_forall_nproper.
intro n.
eapply lemma1.
apply H0.
apply H.
Qed.

Theorem nsound_from_nproper : forall n phi phi' A,
  nproper_rule_gen n A phi phi' -> nsound_rule_gen n A phi phi'.
unfold nproper_rule_gen in *.
unfold nsound_rule_gen in *.
intros.
specialize (H gamma H0 rho H1).
elim H. intros gamma' Htemp.
decompose [and] Htemp.
exists gamma'.
split.
apply tranz_to_star.
assumption.
assumption.
Qed.

Theorem nsound_system_from_nproper_system : forall n A A',
  nproper_system_gen n A A' -> nsound_system_gen n A A'.
unfold nproper_system_gen.
unfold nsound_system_gen.
intros.
eapply List.Forall_impl.
intros.
destruct a.
rewrite <- nsound_rule_gen_iff_nsound'_rule_gen.
apply nsound_from_nproper.
rewrite nproper_rule_gen_iff_nproper'_rule_gen.
apply H0.
assumption.
Qed.

Theorem lemma2 : forall A phi phi',
  forall (proof : PS19 A phi phi'),
    forall n,
      nproper_system n A ->
      nsound_rule n phi phi'.
  intros A phi phi' proof.
  unfold PS19 in proof.
  remember false as strict.
  induction proof as [
    strict Hstrict |
    strict |
    strict |
    strict |
    strict |
    strict |
    strict |
    strict |
    strict A ].
  
  (* ps_refl *)
  intros.
  unfold nsound_rule.
  unfold nsound_rule_gen.
  intros.
  exists gamma.
  split.
  apply rt_refl.
  assumption.
  
  (* ps_axiom *)
  intros n Himpl'.
  
  assert (Himpl: nsound_system n A) by (apply nsound_system_from_nproper_system; assumption).
  rewrite nsound_rule_iff_nsound'_rule.
  eapply forall_in.
  eassumption.
  apply Himpl.

  (* ps_subst *)
  intros n Himpl.

  specialize (IHproof Heqstrict n Himpl).
  unfold nsound_rule in *.
  unfold nsound_rule_gen in *.
  intros.
  specialize (IHproof gamma H (Compose rho0 rho)).
  assert (Hnew: Satisfies gamma (Compose rho0 rho) phi).
  apply (SatApply gamma rho0 phi rho); assumption.
  specialize (IHproof Hnew).
  clear Hnew.
  elim IHproof.  
  intros gamma' Hconj.
  rewrite <- SatApply in Hconj.
  exists gamma'.
  apply Hconj.

  (* ps_trans *)
  intros n Himpl.

  specialize (IHproof1 Heqstrict n Himpl).
  specialize (IHproof2 Heqstrict n Himpl).
  unfold nsound_rule in *. unfold nsound_rule_gen in *.
  intros gamma Hterm rho Hsat.
  specialize (IHproof1 gamma Hterm rho Hsat).
  elim IHproof1. intros gamma'' Hand.
  decompose [and] Hand; clear Hand.
  specialize (IHproof2 gamma'').
  assert (Hn: nterminates_gen n gamma'' SF).
  eapply nterminates_gen_star. apply H. apply Hterm.
  specialize (IHproof2 Hn rho H0).
  elim IHproof2. intros gamma' Hand. decompose [and] Hand; clear Hand.
  exists gamma'.
  split.
  eapply rt_trans. apply H. assumption.
  assumption.
  
  (* ps_case *)
  intros n Himpl.

  specialize (IHproof1 Heqstrict n Himpl).
  specialize (IHproof2 Heqstrict n Himpl).
  unfold nsound_rule in *. unfold nsound_rule_gen in *.
  intros gamma Hterm rho Hsat.
  unfold Or in Hsat.
  autorewrite with SatRewrite in Hsat.
  unfold not in Hsat.
  specialize (IHproof1 gamma Hterm rho).
  specialize (IHproof2 gamma Hterm rho).
  tauto.

  (* ps_lf *)
  intros n Himpl.

  specialize (IHproof Heqstrict n Himpl).
  unfold nsound_rule in *; unfold nsound_rule_gen in *.
  intros gamma Hterm rho Hsat. specialize (IHproof gamma Hterm rho).
  autorewrite with SatRewrite in *.
  decompose [and] Hsat; clear Hsat.
  specialize (IHproof H0).
  elim IHproof. intros x0 Htranz. decompose [and] Htranz.
  exists x0.
  split. assumption. autorewrite with SatRewrite in *.
  split. assumption. setoid_rewrite patternless_formula. apply H1. assumption.

  (* ps_conseq *)
  intros n Himpl.

  specialize (IHproof Heqstrict n Himpl).
  unfold nsound_rule in *; unfold nsound_rule_gen in *.
  intros gamma Hterm rho Hsat. specialize (IHproof gamma Hterm rho).
  assert (Satisfies gamma rho phi1').
  eapply modus_ponens. apply H. apply Hsat.
  specialize (IHproof H1).
  elim IHproof; intros gamma' Hand. decompose [and] Hand.
  exists gamma'. split. assumption.  
  eapply modus_ponens. apply H0. assumption.

  (* ps_abstr *)
  intros n Himpl.
  
  specialize (IHproof Heqstrict).
  unfold nsound_rule in *; unfold nsound_rule_gen in *.
  intros gamma Hterm rho Hsat.
  specialize (IHproof n Himpl gamma Hterm).
  rewrite SatExists in Hsat.
  destruct Hsat as [t Hsat'].
  specialize (IHproof (Update rho X t) Hsat').
  destruct IHproof as [gamma' [Htranz Hsatup]].
  exists gamma'.
  split.
  apply Htranz.
  rewrite (notFree_sat X phi' H).
  apply Hsatup.
  
  (* ps_circ *)
  
  intros n Himpl.

  assert (Himpl': nsound_system n A) by (apply nsound_system_from_nproper_system; assumption).

  rewrite Heqstrict in *; clear Heqstrict; clear strict.
  clear IHproof1.
  clear proof2.
  assert (IHproof1: forall n : nat, nproper_system n A -> nproper_rule n phi phi'').
  apply lemma1. apply proof1.

  assert (forall m : nat, m <= n -> nproper_rule m phi phi').
  induction m as [ | m' ].
  (* m = 0 *)
  intros. unfold nproper_rule; unfold nproper_rule_gen.
  intros gamma Hterm rho Hsat. inversion Hterm.
  (* m = S m' *)
  intros Hcond.
  assert (Hmweak : m' <= n) by (apply le_Sn_le; assumption).
  specialize (IHm' Hmweak).
  specialize (IHproof1 n Himpl).
  specialize (IHproof2 (eq_refl false) m').
  assert (Hpropersystem : nproper_system m' ((phi, phi') :: A)%list).
  constructor.
  rewrite <- nproper_rule_gen_iff_nproper'_rule_gen.
  apply IHm'.
  eapply nproper_system_weaken.
  apply Himpl.
  assumption.
  specialize (IHproof2 Hpropersystem).
  assert (IHproof1' : nproper_rule (S m') phi phi'').
  eapply nproper_rule_weaken.
  apply IHproof1.
  assumption.
  eapply rule_transitivity'.
  eapply nproper_rule_weaken.
  apply IHproof1.
  assumption.
  apply IHproof2.
  apply nsound_from_nproper.
  apply H.
  apply le_refl.
Qed.

Theorem partial_correctness : forall A : System, forall phi phi' : Formula,
  proper_system A ->
  PS19 A phi phi' ->
  sound_rule_gen SF phi phi'.
intros.
unfold proper_system in *.
rewrite proper_system_forall_nproper_system in H.
rewrite sound_forall_nsound.
intros.
eapply lemma2.
apply H0.
apply H.
Qed.

End MatchLPartialCorrectness.
