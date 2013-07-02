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
    (exists rho, phi rho gamma /\ phi' rho gamma') ->
    ts S gamma gamma'.

Section FixBaseSystem.

(* underlying transition relation *)
Variable SF : cfg -> cfg -> Prop.

Inductive all_reach (env : Type) (phi : formula cfg env) (rho : env) (gamma : cfg) : bool -> Prop :=
  | reach_here : phi rho gamma -> all_reach phi rho gamma false
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
    trace_hits (fun cfg => phi rho cfg) t
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
    exists gamma', clos SF strict gamma gamma' /\ phi rho gamma'.
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

Definition successors (P : cfg -> Prop) : cfg -> Prop :=
  fun c => forall c', SF c c' -> P c'.

Lemma under_terminates : forall (P : cfg -> Prop) (c : cfg),
  terminates c SF ->
  (forall c', clos SF false c c' -> successors P c' -> P c') ->
  P c.
Proof.
induction 1.
intros.
apply H1.
constructor.
unfold successors; intros.
apply H0.
assumption.
intros c'0 Hstep.
apply H1.
refine (clos_trans _ Hstep).
apply clos_step. assumption.
Qed.

Definition always (P : cfg -> Prop) : cfg -> Prop :=
  fun c => forall c', clos SF false c c' -> P c'.

Lemma always_fwd (P : cfg -> Prop) :
  forall strict g g',
    clos SF strict g g' ->
    always P g -> always P g'.
Proof.
unfold always; intros.
apply H0.
assert (clos SF false g g') by (destruct strict;auto using clos_unstrict).
eauto using clos.
Qed.

Lemma succ_always_strict_fwd (P : cfg -> Prop) :
  forall g g',
    clos SF true g g' ->
    successors (always P) g -> always P g'.
Proof.
intros.
rewrite clos_iff_left in H.
inversion H; subst.
auto.
rewrite <- clos_iff_left in H2.
specialize (H0 _ H1).
eauto using always_fwd.
Qed.

(* at points under gamma, the rule holds semantically *)
Definition gamma_entails parent strict env
  (phi phi' : formula cfg env) :=
  forall rho gamma,
    clos SF false parent gamma ->
    phi rho gamma ->
    all_reach phi' rho gamma strict.

Definition gamma_entails_alt strict env (phi phi' : formula cfg env) :=
  always (fun g => forall rho, phi rho g -> all_reach phi' rho g strict).

Lemma entails : forall p s env (phi phi' : formula cfg env),
  gamma_entails p s phi phi' <-> gamma_entails_alt s phi phi' p.
firstorder.  
Qed.

Definition gamma_succ_entails parent strict env
  (phi phi' : formula cfg env) :=
  forall gamma', SF parent gamma' -> gamma_entails gamma' strict phi phi'.

Definition gamma_succ_entails_alt strict env (phi phi' : formula cfg env) :=
  successors (gamma_entails_alt strict phi phi').

Lemma succ_entails : forall p s env (phi phi' : formula cfg env),
  gamma_succ_entails p s phi phi' <-> gamma_succ_entails_alt s phi phi' p.
firstorder.  
Qed.

Lemma gamma_entails_fwd :
  forall (gamma gamma' : cfg),
    clos SF false gamma gamma' ->
    forall strict env (phi phi' : formula cfg env),
      gamma_entails gamma strict phi phi'->
      gamma_entails gamma' strict phi phi'.
Proof.
  unfold gamma_entails. intros. eauto using clos_trans.
Qed.

Lemma gamma_succ_entails_strict_fwd :
  forall (gamma gamma' : cfg),
    clos SF true gamma gamma' ->
    forall strict env (phi phi' : formula cfg env),
      gamma_succ_entails gamma strict phi phi'->
      gamma_entails gamma' strict phi phi'.
Proof.
  intros. rewrite clos_iff_left in H.
  inversion H;subst.
  firstorder.
  specialize (H0 _ H1).
  rewrite <- clos_iff_left in H2.
  revert H0.
  apply gamma_entails_fwd.
  apply clos_unstrict.
  assumption.
Qed.

Definition gamma_entails_system parent strict (S : system cfg) :=
  forall env (phi phi' : formula cfg env), S env phi phi' ->
    gamma_entails parent strict phi phi'.

Definition gamma_entails_system_alt strict (S : system cfg) :=
  always (fun g => forall env (phi phi' : formula cfg env), S env phi phi' ->
                   forall rho, phi rho g -> all_reach phi' rho g strict).

Lemma entails_system : forall p s S,
  gamma_entails_system p s S <-> gamma_entails_system_alt s S p.
firstorder.
Qed.

Definition gamma_succ_entails_system parent strict (S : system cfg) :=
  forall gamma', SF parent gamma' -> gamma_entails_system gamma' strict S.

Definition gamma_succ_entails_system_alt strict (S : system cfg) :=
  successors (gamma_entails_system_alt strict S).

Lemma succ_entails_system : forall p s S,
  gamma_succ_entails_system p s S <-> gamma_succ_entails_system_alt s S p.
unfold gamma_succ_entails_system, gamma_succ_entails_system_alt, successors.
intuition;apply entails_system; auto.
Qed.

Lemma gamma_system_fwd : forall gamma gamma' strict S,
  clos SF false gamma gamma' ->
  gamma_entails_system gamma strict S ->
  gamma_entails_system gamma' strict S.
Proof.
  unfold gamma_entails_system.
  intuition.
  eauto using gamma_entails_fwd.
Qed.

Lemma clos_ext : forall a b c strict,
                   SF a b -> clos SF strict b c -> clos SF strict b c.
eauto using clos,clos_unstrict.
Qed.

Lemma all_reach_impl_path :
  forall env (phi : formula cfg env) rho env' (phi' : formula cfg env') rho' gamma strict,
    (forall gamma', clos SF false gamma gamma' ->  phi rho gamma' -> phi' rho' gamma') ->
    all_reach phi rho gamma strict ->
    all_reach phi' rho' gamma strict.
Proof.
intros. induction H0.
eauto using all_reach, clos.
apply reach_later;eauto using all_reach, clos, clos_ext.
Qed.

Lemma all_reach_impl :
  forall env (phi : formula cfg env) rho env' (phi' : formula cfg env') rho' gamma strict,
    (forall gamma, phi rho gamma -> phi' rho' gamma) ->
    all_reach phi rho gamma strict ->
    all_reach phi' rho' gamma strict.
Proof.
intros. induction H0; auto using all_reach.
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
  subst. trivial.
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

Require Import Bool.

Lemma all_reach_join : forall env (phi : formula cfg env) rho g strict1 strict2,
  all_reach (fun rho g => all_reach phi rho g strict1) rho g strict2 ->
  all_reach phi rho g (orb strict1 strict2).
intros.
induction H;rewrite orb_false_r in * |- *.
assumption.
apply reach_later.
assumption.
intros.
specialize (H0 _ H2).
specialize (H1 _ H2).
destruct strict1;[apply all_reach_unstrict|];assumption.
Qed.

Lemma gamma_entails_trans_nonstrict :
  forall gamma env (phi phi' phi'' : formula cfg env),
    gamma_entails gamma false phi phi' ->
    gamma_entails gamma false phi' phi'' ->
    gamma_entails gamma false phi phi''.
Proof.
  unfold gamma_entails; intros.
  specialize (H _ _ H1 H2).
  apply (@all_reach_join _ _ _ _ false false).
  revert H.
  apply all_reach_impl_path; eauto using clos_trans.
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

Theorem soundness : forall C S env phi phi',
  forall (proof : IS cfg SF C S env phi phi'),
    forall gamma,
      terminates gamma SF ->
      gamma_entails_system gamma true S ->
      match C with
          | None => True
          | Some c => gamma_succ_entails_system gamma true c
      end ->
      gamma_entails gamma (match C with None => false | Some _ => true end) phi phi'.
Proof.
  intros until phi'; intro proof.
  induction proof; intros gamma Hterm Hsystem HCsystem.

(* step *)
+ unfold gamma_entails; intros.
  destruct (H _ _ H1).
  apply reach_later.
  assumption.
  auto using all_reach.

(* axiom *)
+ apply gamma_entails_unstrict. auto.

(* refl *)
+ destruct C;[destruct H|].
  unfold gamma_entails; auto using all_reach.

(* trans *) 
+ destruct C.
  (* true case where we need to take steps *)
  apply gamma_entails_trans with phi'.
  apply IHproof1; assumption.
  intros.
  apply IHproof2.
  eauto using terminates_fwd.
  simpl.
  assert (gamma_entails_system gamma' true A) by (eauto using clos_unstrict, gamma_system_fwd).
  assert (gamma_entails_system gamma' true s).
    rewrite entails_system.
    rewrite succ_entails_system in HCsystem.
    eapply succ_always_strict_fwd;eassumption.
  clear -H0 H1.
  unfold gamma_entails_system in H0, H1 |- *.
  intros.
  firstorder.
  trivial.
  (* false case, where we don't need to prove anything about C *)
  specialize (IHproof1 _ Hterm Hsystem I).
  specialize (IHproof2 _ Hterm Hsystem I).
  clear -IHproof1 IHproof2.
  eapply gamma_entails_trans_nonstrict;eassumption.

(* ps_conseq *)
+ specialize (IHproof gamma Hterm Hsystem HCsystem).
  intros rho gamma0; intros.
  apply H in H2.
  specialize (IHproof rho gamma0 H1 H2).
  revert IHproof.
  apply all_reach_impl.
  auto.

(* ps_case *)
+ solve[firstorder].

(* ps_abstr *)
+ specialize (IHproof gamma Hterm Hsystem HCsystem).
  intro; intros.
  destruct H0.
  specialize (IHproof (rho , x) gamma0 H H0).
  revert IHproof. apply all_reach_impl. auto.

(* ps_circ *)
+ apply gamma_entails_unstrict.
  pattern gamma.
  apply under_terminates.
  assumption.
  intros.
  apply IHproof.
  eauto using terminates_fwd.
  eauto using gamma_system_fwd.
  simpl.
  unfold gamma_succ_entails_system, gamma_entails_system.
  intros.
  destruct H2.
  destruct C;[|destruct H2].
  simpl in H2.
  assert (clos SF true gamma gamma').
  eapply clos_cons_rt. eassumption. constructor (assumption).
  apply gamma_succ_entails_strict_fwd with gamma.
  assumption.
  clear -H2 HCsystem.
  unfold gamma_succ_entails. intros.
  specialize (HCsystem _ H _ _ _ H2). assumption.
  destruct H2 as [<- []].
  unfold eq_rect_r, eq_sym in H2, H3; simpl in H2, H3; subst phi0 phi'0.
  specialize (H0 _ H1); simpl in H0.
  assumption.

(* subst *)
+ specialize (IHproof gamma Hterm Hsystem HCsystem); clear -IHproof.
  unfold gamma_entails in * |- *; intros.
  specialize (IHproof (f rho) gamma0 H H0).
  revert IHproof.
  apply all_reach_impl.
  trivial.

(* ps_lf *)
+ specialize (IHproof gamma Hterm Hsystem HCsystem).
  revert IHproof; clear.
  intro; intro; intros.
  destruct H0.
  specialize (IHproof rho gamma0 H H0).
  clear -IHproof H1.
  revert IHproof; apply all_reach_impl. auto.
Qed.

Definition empty_system : system cfg := fun env phi phi' => False.
Lemma empty_system_vacuous : forall gamma,
  gamma_entails_system gamma true empty_system.
unfold gamma_entails_system; simpl; intros.
destruct H.
Qed.

Theorem simple_soundness : forall env phi phi',
  IS cfg SF None empty_system env phi phi' ->
  forall gamma : cfg, terminates gamma SF ->
  forall rho, phi rho gamma -> all_reach phi' rho gamma false.
intros.
eapply soundness with (C:= None); eauto using empty_system_vacuous, clos_refl.
Qed.

End FixBaseSystem.
End domain.
