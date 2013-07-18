Require Import generic_soundness.

Add LoadPath "../ml_proof".

Require Import reduction.

Require Import proofsystem.
Set Implicit Arguments.

Require Import Setoid.
Require Import Relation_Definitions.

Axiom cfg : Set.
Axiom S : cfg -> cfg -> Prop.

(* Lemmas *)
Lemma clos_lift (A B : Type) (R1 : relation A) (R2 : relation B)
  (f : B -> A) :
  (forall x y, R1 x y -> forall x', x = f x' -> exists y', R2 x' y' /\ y = f y') ->
  forall strict x y,
  clos R1 strict x y ->
  forall x', x = f x' ->
  exists y', clos R2 strict x' y' /\ y = f y'.
induction 2;intros;
repeat match goal with
         | [H : _ -> _ -> ?R _ _ -> _, H1 : ?R _ _ |- _] => specialize (H _ _ H1)
         | [H : forall x, ?a = f x -> _, H1 : ?a = f _ |- _] => specialize (H _ H1)
         | [H : exists y', _ /\ _ = f y' |-_] =>
           destruct H as [? []]
       end;
eauto using clos.
Qed.

Lemma terminates_next : forall {A : Set} {R : relation A} (a : A),
  terminates a R -> forall b, R a b -> terminates b R.
destruct 1.
assumption.
Qed.

Lemma under_terminates : forall {A : Set} {R : relation A} (a : A),
  terminates a R -> forall (P : A -> Prop),
  (forall a0, clos R false a a0 ->
              (forall a', R a0 a' -> P a') ->
              P a0)
  -> P a.
intros A R a term P.
move term after P.
induction term as [a HAcc IH].
intro Hlater.
apply Hlater.
constructor.
intros a' Raa.
apply IH.
assumption.
intros a0 Ha'a0 Hnext.
apply Hlater.
clear -Raa Ha'a0. eauto using clos.
assumption.
Qed.

Lemma clos_cat'
     : forall (A : Type) (R : relation A) (a : A) (s1 : bool) 
         (b : A) (s2 s3 : bool) (c : A),
       clos R s1 a b -> clos R s2 b c -> implb s3 (s1 || s2) = true -> clos R s3 a c.
intros.
pose proof (clos_cat H H0) as H2; clear -H1 H2.
destruct s3. simpl in H1; rewrite H1 in H2;assumption.
destruct (orb s1 s2);auto using clos_unstrict.
Qed.

Module ExPathSemantics <: ReachabilitySemantics.

(* Definitions *)
Definition index : Set := {gamma : cfg | terminates gamma S}.
Definition ix_rel (i1 i2 : index) : Prop :=
  S (proj1_sig i1) (proj1_sig i2).

Definition holds' strict env (phi phi' : formula cfg env) : cfg -> Prop :=
  fun parent =>
    forall rho gamma1,
      clos S false parent gamma1 ->
      phi rho gamma1 ->
      exists gamma2, clos S strict gamma1 gamma2 /\ phi' rho gamma2.
Definition holds strict env phi1 phi2 (i : index) := @holds' strict env phi1 phi2 (proj1_sig i).

(* Nontrivial proofs *)
(** Circularity **)
Lemma ix_rel_ind : forall env (phi phi' : formula cfg env),
      forall i0,
      (forall i, clos ix_rel false i0 i ->
                   (forall i', ix_rel i i' -> holds true phi phi' i') ->
                   holds true phi phi' i)
       -> holds true phi phi' i0.
intros env phi phi' i Hix_later.
destruct i as [a Hterm].
unfold holds. simpl.
apply (under_terminates Hterm).
intros a0 Haa0 Hnext.

assert (exists i', clos ix_rel false (exist _ a Hterm) i' /\ a0 = proj1_sig i').
  clear -Haa0. apply clos_lift with (R1:=S) (x:=a);[|assumption|reflexivity].
  intros.
  destruct x';simpl in *|- *;subst.
  assert (terminates y S) by (destruct t as [H0]; apply H0; assumption).
  exists (exist _ y H0). split;[|reflexivity].
  unfold ix_rel;simpl. assumption.
destruct H as [i' [Hreach Hend]].
specialize (Hix_later i' Hreach).
rewrite Hend.
apply Hix_later.
intros.
apply Hnext.
rewrite Hend.
exact H.
Qed.

Create HintDb holds_solve discriminated.
Hint Transparent holds holds' : holds_solve.
Hint Unfold holds' : holds_solve.

Ltac clear_except_path :=
repeat match goal with
  | [H : ?Hyp |- _] =>
    match Hyp with
      | terminates _ _ => fail 1
      | clos _ _ _ _ => fail 1
      | S ?x ?y => apply (clos_step _ true) in H
      | _ => clear H
    end
  end.
Ltac clos_solve :=
  clear_except_path;
match goal with
  | [|- clos _ false ?x ?x] => apply clos_refl
  | [|- clos _ false _ _] =>
    repeat match goal with
             | [H : clos _ true _ _ |- _] => apply clos_unstrict in H
           end;
    repeat match goal with
             | [H : clos ?S _ ?x ?y |- clos ?S _ ?x ?y ] => assumption
             | [H : clos ?S _ ?x ?y, H2 : clos ?S _ ?y _ |- clos ?S _ ?x _ ] =>
               pose proof (clos_trans H H2); clear H2
           end
  | [|- clos _ _ _ _] =>
    repeat match goal with
         | [H : clos ?S ?f ?x ?y |- clos ?S ?f ?x ?y ] => assumption
         | [H : clos ?S true ?x ?y, H2 : clos ?S _ ?y _ |- clos ?S _ ?x _ ] =>
           pose proof (clos_cons_lt H H2); clear H H2
         | [H : clos ?S _ ?x ?y, H2 : clos ?S true ?y _ |- clos ?S _ ?x _ ] =>
           pose proof (clos_cons_rt H H2); clear H H2
      end
end.

Hint Extern 0 (clos _ _ _ _) => clos_solve : holds_solve.

Ltac holds_start := intros;
  repeat match goal with
  (* open unnecessary uses of holds/indices *)
  | [i : index |- _] => destruct i
  | [H : holds _ _ _ (exist _ _ _) |- _] => unfold holds in H;simpl proj1_sig in H
  | [|- holds _ _ _ (exist _ _ _)] => unfold holds;simpl proj1_sig;unfold holds';intros
  | [H : ix_rel (exist _ _ _) _ |- _] => unfold ix_rel in H; simpl proj1_sig in H
  | [H : ix_rel _ (exist _ _ _) |- _] => unfold ix_rel in H; simpl proj1_sig in H
  (* Instantate a hypothesis quantified over ix_rel, as appears in strict trans *)
  | [H : forall i', ix_rel (exist _ ?x ?t) i' -> holds _ ?phi _ i',
       Hphi : ?phi _ ?x0 |- _ ] =>
    let Hprog := fresh "Hprog" in
    assert (clos S true x x0) as Hprog by clos_solve;
    let x1 := fresh "x1" with Hstep := fresh "Hstep" with Hreach := fresh "Hreach" in
    apply clos_true_step in Hprog; destruct Hprog as [x1 [Hstep Hreach]];
    specialize (H (exist _ x1 (terminates_next t _ Hstep)) Hstep)
  (* Use holds' hypotheses *)
  | [H : holds' _ ?phi _ ?x, Hphi : ?phi _ ?gamma |- _]=>
    let Hreach := fresh "Hreach" in
    assert (clos S false x gamma) as Hreach by clos_solve;
    specialize (H _ _ Hreach Hphi)
  | [H : exists _, clos S _ _ _ /\ _ |- _] => destruct H as [? []]
  end.
Ltac holds_finish :=
  solve[eauto with holds_solve
       |intuition
          (repeat match goal with
             | [H : forall _ _, ?phi _ _ -> _, Hphi : ?phi _ _ |- _] =>
               specialize (H _ _ Hphi)
           end;firstorder with holds_solve)
       ].
Ltac holds_tac := holds_start;holds_finish.

(** Transitivity **)
Lemma holds_trans_strict : forall env phi phi' phi'' i,
    @holds true env phi phi' i ->
    (forall i' : index, ix_rel i i' -> holds false phi' phi'' i') ->
   holds true phi phi'' i.
holds_tac.
Qed.

Lemma holds_trans : forall env phi phi' phi'' i,
    @holds false env phi phi' i ->
    holds false phi' phi'' i ->
    holds false phi phi'' i.
holds_tac.
Qed.

Lemma holds_strict_later : forall env phi1 phi2 i,
                             @holds true env phi1 phi2 i ->
                             forall i', ix_rel i i' ->
                                        holds true phi1 phi2 i'.
holds_tac.
Qed.

Lemma holds_unstrict : forall env phi1 phi2 i,
                         @holds true env phi1 phi2 i -> holds false phi1 phi2 i.
holds_tac.
Qed.

Lemma holds_step : forall env (phi phi' : formula cfg env),
    (forall (e : env) (c : cfg),
      phi e c ->
      (exists c2 : cfg, S c c2) /\ (forall c2 : cfg, S c c2 -> phi' e c2)) ->
    forall i, holds true phi phi' i.
holds_tac.
Qed.

Lemma holds_refl : forall env phi i, @holds false env phi phi i.
holds_tac.
Qed.

Lemma holds_case :
    forall strict env (phi phi1 phi' : formula cfg env) i,
      holds strict phi phi' i -> holds strict phi1 phi' i ->
      holds strict (fun (e : env) (g : cfg) => phi e g \/ phi1 e g) phi' i.
holds_tac.
Qed.

Lemma holds_mut_conseq :
    forall strict env1 (phi1 phi2 : formula cfg env1)
                  env2 (phi1' phi2' : formula cfg env2),
     (forall gamma rho,
        phi1 rho gamma ->
        exists rho', phi1' rho' gamma /\
                     forall gamma', phi2' rho' gamma' -> phi2 rho gamma') ->
    forall i, holds strict phi1' phi2' i ->
              holds strict phi1 phi2 i.
holds_tac.
Qed.

Definition cfg := cfg.
Definition S := S.
End ExPathSemantics.

Module ExPathSoundness := Soundness ExPathSemantics.

Definition holds strict env (phi phi' : formula cfg env) :=
  forall rho gamma, terminates gamma S ->
    phi rho gamma -> exists gamma', phi' rho gamma' /\ clos S strict gamma gamma'.

Lemma approx_holds env (phi phi' : formula cfg env) strict :
  (forall i, ExPathSemantics.holds strict phi phi' i) ->
  holds strict phi phi'.
intro H. unfold holds.
intros.
specialize (H (exist _ gamma H0) _ _ (clos_refl _ _) H1).
firstorder.
Qed.

Lemma holds_approx env (phi phi' : formula cfg env) strict :
  holds strict phi phi' ->
  (forall i, ExPathSemantics.holds strict phi phi' i).
intros Hstrong i.
destruct i as [gamma term].
unfold ExPathSemantics.holds, ExPathSemantics.holds'.
intros rho gamma1 Hreach Hphi.
specialize (Hstrong _ gamma1 (terminates_fwd term Hreach) Hphi).
firstorder.
Qed.

Definition system_holds (A : system cfg) :=
  forall env phi1 phi2, @A env phi1 phi2 -> holds true phi1 phi2.

Theorem soundness (A : system cfg) env (phi1 phi2 : formula cfg env) :
  IS cfg S None A env phi1 phi2 ->
  system_holds A ->
  holds false phi1 phi2.
Proof.
intros pf HA.
apply approx_holds.
intro i.
apply (ExPathSoundness.soundness pf);trivial.
clear -HA i.
pose proof holds_approx.
unfold ExPathSoundness.system_holds;intros.
eauto.
Qed.
