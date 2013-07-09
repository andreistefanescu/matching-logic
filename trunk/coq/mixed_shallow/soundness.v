Add LoadPath "../ml_proof".

Require Import reduction.

Require Import proofsystem.
Set Implicit Arguments.

Require Import Setoid.
Require Import Relation_Definitions.

Section domain.
Variable cfg : Set.

(* step according to a system *)
(*
Inductive ts (S : system cfg) : cfg -> cfg -> Prop :=
  | ts_step : forall gamma gamma' env phi phi',
    S env phi phi' ->
    (exists rho, phi rho gamma /\ phi' rho gamma') ->
    ts S gamma gamma'.
 *)

Section FixBaseSystem.

(* underlying transition relation *)
Variable SF : cfg -> cfg -> Prop.

Definition unstuck c := exists c', SF c c'.

Definition anySuccessors (P : cfg -> Prop) : cfg -> Prop :=
  fun c => forall c', SF c c' -> P c'.
Definition someSuccessor (P : cfg -> Prop) : cfg -> Prop :=
  fun c => exists c', SF c c' /\ P c'.
Definition successors (P : cfg -> Prop) : cfg -> Prop :=
  fun c => (exists c', SF c c') /\ anySuccessors P c.

Definition suc_if_nonempty (C : option (system cfg)) (P : cfg -> Prop) : cfg -> Prop :=
  match C with
    | Some _ => anySuccessors P
    | None => P
  end.

Definition strong (f : flag) : (cfg -> Prop) -> cfg -> Prop :=
  match f with
    | all_path => successors
    | ex_path => someSuccessor
  end.

CoInductive all_reach (P : cfg -> Prop) (c : cfg) : Prop :=
  | all_here : P c -> all_reach P c
  | all_later : successors (all_reach P) c -> all_reach P c
  .
CoInductive ex_reach (P : cfg -> Prop) (c : cfg) : Prop :=
  | ex_here : P c -> ex_reach P c
  | ex_later : someSuccessor (ex_reach P) c -> ex_reach P c
  .
CoFixpoint all_join (P : cfg -> Prop) (c : cfg) : all_reach (all_reach P) c -> all_reach P c :=
  fun H => match H with
   | all_here r => r
   | all_later (conj s l) => all_later (conj s (fun c' step => all_join (l c' step)))
  end.
CoFixpoint ex_join (P : cfg -> Prop) (c : cfg) : ex_reach (ex_reach P) c -> ex_reach P c :=
  fun H => match H with
   | ex_here r => r
   | ex_later (ex_intro c' (conj step l)) => ex_later (ex_intro _ c' (conj step (ex_join l)))
  end.
Definition reach f P :=
  match f with
    | all_path => all_reach P
    | ex_path => ex_reach P
  end.
Definition reach_join f : forall P c, reach f (reach f P) c -> reach f P c.
destruct f;[apply all_join|apply ex_join].
Qed.

Lemma reach_here : forall f (P : cfg -> Prop) c, P c -> reach f P c.
destruct f;intros;[apply all_here|apply ex_here];assumption.
Qed.

Definition next f P :=
  match f with
    | all_path => successors P
    | ex_path => someSuccessor P
  end.
Definition reach_strict (strict : bool) f P :=
  if strict then next f (reach f P) else reach f P.

Definition rule_holds {env} (r : rule cfg env) :=
  match r with
    | Rule f phi phi' => fun c => forall rho,
                                    phi rho c -> reach f (phi' rho) c
  end.

Definition rule_holds_strict strict {env} (r : rule cfg env) :=
  match r with
    | Rule f phi phi' => fun c => forall rho,
                                    phi rho c -> reach_strict strict f (phi' rho) c
  end.

Definition Impl (P Q : cfg -> Prop) : cfg -> Prop :=
  fun c => P c -> Q c.

Definition valid (P : cfg -> Prop) : Prop :=
  forall c, P c.

Definition always (P : cfg -> Prop) : cfg -> Prop :=
  fun c => forall c', clos SF false c c' -> P c'.

Lemma always_here (P : cfg -> Prop) :
  forall c, always P c -> P c.
Proof.
auto using clos_refl.
Qed.

Lemma valid_always : forall (P : cfg ->  Prop) gamma, valid P -> always P gamma.
firstorder.
Qed.
Arguments valid_always [P] gamma H _ _.

Definition always_lift : forall (P Q R : cfg -> Prop),
                           (forall c, P c -> Q c -> R c) ->
                           (forall c, always P c -> always Q c -> always R c).
firstorder.
Qed.

Definition anysuc_lift : forall (P Q R : cfg -> Prop),
                           (forall c, P c -> Q c -> R c) ->
                           (forall c, anySuccessors P c -> anySuccessors Q c -> anySuccessors R c).
firstorder.
Qed.

Definition suc_if_lift : forall C (P Q R : cfg -> Prop),
                           (forall c, P c -> Q c -> R c) ->
                           (forall c, suc_if_nonempty C P c ->
                                      suc_if_nonempty C Q c ->
                                      suc_if_nonempty C R c).
destruct C;[exact anysuc_lift|trivial].
Qed.

Definition next_any_lift : forall f (P Q R : cfg -> Prop),
                             (forall c, P c -> Q c -> R c) ->
                             (forall c, anySuccessors P c -> next f Q c -> next f R c).
destruct f;firstorder.
Qed.

Definition reach_always_lift : forall f (P Q R : cfg -> Prop),
                                 (forall c, P c -> Q c -> R c) ->
                                 (forall c, always P c -> reach f Q c -> reach f R c).
Proof.
intros until 1.
destruct f.
cofix.
intros.
destruct H1.
exact (all_here _ _ (H _ (always_here H0) H1)).
destruct H1.
apply all_later. split;[assumption|].
unfold anySuccessors. intros. apply reach_always_lift; clear reach_always_lift;simpl.
unfold always in * |- *. intros. apply H0. eauto using clos. auto.

cofix.
intros.
destruct H1.
exact (ex_here _ _ (H _ (always_here H0) H1)).
destruct H1 as [x []].
apply ex_later. exists x;split;[assumption|].
apply reach_always_lift; clear reach_always_lift.
unfold always in * |- *. intros. apply H0. eauto using clos. auto.
Qed.

Lemma always_always P : forall c,
  always P c -> always (always P) c.
Proof.
unfold always. intuition. eauto using clos_trans.
Qed.

Lemma always_any P : forall c,
  always P c -> anySuccessors P c.                     
Proof.
firstorder using clos_step.
Qed.

Lemma always_suc_if (C : option (system cfg)) P : forall c,
  always P c -> suc_if_nonempty C P c.                     
Proof.
destruct C;simpl;auto using always_any, clos_refl.
Qed.

Definition MP : forall (P Q : cfg -> Prop), valid (Impl (Impl P Q) (Impl P Q)).
firstorder.
Qed.

Definition reach_strict_always_lift : forall s f (P Q R : cfg -> Prop),
  (forall c, P c -> Q c -> R c) ->
  (forall c, always P c -> reach_strict s f Q c -> reach_strict s f R c).
Proof.
destruct s;[|exact reach_always_lift].
intros until 2.
generalize (always_any (always_always H0)).
simpl; eauto using next_any_lift, reach_always_lift.
Qed.

(*
Definition reach_always_lift : forall f (P Q R : cfg -> Prop),
                             (forall c, P c -> Q c -> R c) ->
                             (forall c, always P c -> reach f Q c -> reach f R c).
intros until 1; destruct f; cofix; intros;
(destruct H1;
[clear reach_always_lift; apply reach_here; auto using clos_refl|]).
apply all_later.
destruct H1;split;[assumption|].
intro;intro. apply reach_always_lift;clear reach_always_lift.
Qed.
*)

Lemma valid_impl_always (P Q : cfg -> Prop) : forall c,
  valid (Impl P Q) -> always P c -> always Q c.
firstorder.
Qed.

Lemma always_impl_always (P Q : cfg -> Prop) : forall c,
  always (Impl P Q) c -> always P c -> always Q c.
firstorder.
Qed.

Lemma always_impl_always_always (P Q : cfg -> Prop) : forall c,
  always (Impl (always P) Q) c -> always P c -> always Q c.
Proof.
intros. eauto using always_impl_always, always_always.
Qed.

Definition system_holds (S : system cfg) : cfg -> Prop :=
  fun c => forall env r, @S env r -> rule_holds_strict true r c.

Lemma union_system_split : forall (S1 S2 : system cfg) (P : cfg -> Prop),
  valid (Impl (always (system_holds (union_system S1 S2))) P) ->
  valid (Impl (always (system_holds S1))
        (Impl (always (system_holds S2))
              P)).
firstorder.
Qed.

Lemma always_suc_always P : forall c,
  always P c -> anySuccessors (always P) c.                             
Proof.
unfold always, anySuccessors.
intros.
eauto using clos.
Qed.

Lemma always_impl_all_reach (P Q : cfg -> Prop) : forall c,
  all_reach P c -> always (Impl P Q) c -> all_reach Q c.
cofix.
  intros.
  destruct H.
  clear always_impl_all_reach.
  apply all_here; apply H0; auto using clos_refl.
  apply all_later.
  destruct H.
  split;[assumption|].
  apply always_suc_always in H0.
  unfold anySuccessors in * |- *.
  auto.
Qed.

Lemma clos_forget_progress
     : forall (A : Type) (R : relation A) s (a b : A),
       clos R s a b -> clos R false a b.
Proof.
destruct s;auto using clos_unstrict.
Qed.

Lemma suc_always_always P : forall c,
  anySuccessors (always P) c -> always (anySuccessors (always P)) c.
Proof.
intros.
unfold anySuccessors in H.
unfold always at 1.
intros.
rewrite clos_iff_left in H0.
destruct H0;[assumption|..];apply always_suc_always;auto.
rewrite <- clos_iff_left in H1.
apply clos_forget_progress in H1.
specialize (H _ H0).
apply always_always in H.
auto.
Qed.

Lemma next_impl (P Q : cfg -> Prop):
  (forall c, P c -> Q c) -> forall f c, next f P c -> next f Q c.
Proof. destruct f;firstorder. Qed.

Lemma rule_holds_weak {env} (r : rule cfg env) s (c : cfg) :
  rule_holds_strict true r c -> rule_holds_strict s r c.
destruct s. trivial.
destruct r.
simpl; intros.
specialize (H _ H0).
destruct f;[apply all_later|apply ex_later];assumption.
Qed.

Lemma circ_hyp_restate : forall (C : option (system cfg)) gamma,
   anySuccessors (always (system_holds (system_opt C))) gamma ->
   suc_if_nonempty C (always (always (system_holds (system_opt C)))) gamma.
destruct C;simpl;unfold anySuccessors;
[auto using always_always|firstorder using always_always].
Qed.

Theorem soundness : forall C S env (r : rule cfg env),
  forall (proof : IS SF C S r),
    forall gamma,
      always (system_holds S) gamma ->
      anySuccessors (always (system_holds (system_opt C))) gamma ->
      rule_holds_strict (match C with
        | None => false
        | Some _ => true
      end) r gamma.
Proof.
  intros until r; induction 1; intros gamma Hsystem Hcsystem;
  repeat match goal with
      [ r : rule _ _ |- _ ] =>destruct r
  end.

Ltac introduceAs ty H :=
  match goal with
    | [H : ty |- _] => fail 1 "already have hypothesis" H "of type" ty
    | _ => assert ty by exact H
  end.
Ltac introduce H := let t := type of H in introduceAs t H.
Ltac introduce2 H1 H2 := (introduce H1 ; try (introduce H2)) || introduce H2.
Ltac fwd_clos :=
  match goal with
      (* and instantiate IH *)
    | [ H : valid (Impl (always ?P) ?Q), HA : always ?P ?c |- _] =>
      introduce (valid_impl_always H (always_always HA)) 
    | [ H : always (Impl (always ?P) ?Q), HA : always ?P ?c |- _] =>
      introduce (always_impl_always H (always_always HA)) 
    | [ H : always (Impl (anySuccessors (always ?P)) ?Q) ?c,
            HA : anySuccessors (always ?P) ?c |- _] =>
      introduce (always_impl_always H (suc_always_always HA)) 
    | [ IH : forall gamma, always (system_holds ?S) gamma ->
                             anySuccessors (always (system_holds (system_opt ?C))) gamma ->
                             ?P gamma |- _] =>
        change (valid (Impl (always (system_holds S))
                      (Impl (anySuccessors (always (system_holds (system_opt C))))
                            P))) in IH
    | [ Hrule : rule_holds_strict ?s (Rule _ ?phi _) ?c,
        Hphi : ?phi _ ?c |- _] =>
      introduce (Hrule _ Hphi)
    | [ phi : formula _ _ |- _] =>
      match goal with
        (* expand formula satisfaction to strong all_reach+ex_reach satisfaction *)
        | [H : next _ (phi _) _ |- _] =>
          introduce2 (next_impl _ _ (all_here _) _ _ H)
                     (next_impl _ _ (ex_here _) _ _ H)
        (* expand formula satisfaction to weak all_reach+ex_reach satisfaction *)
        | [H : phi _ _ |- _] =>
          introduce2 (all_here _ _ H) (ex_here _ _ H)
        (* Specialize formula satisfaction, quantified over env or env+cfg *)
        | [H : forall e, ?phi e ?c -> _, H0 : phi _ ?c |- _] =>
          introduce (H _ H0)
        | [H : forall e c, phi e c -> _, H0 : phi _ _ |- _] =>
          introduce (H _ _ H0)
      end
      (* Specialize system satisfaction *)
    | [ Hsys : system_holds ?Sys _, Hrule : ?Sys _ _|-_] =>
        introduce (Hsys _ _ Hrule)
      (* localize always *)
    | [H : always _ ?g |- _] =>
        introduce (H _ (clos_refl _ g))
  end.

  + (* All step *)
    clear -H.
    change (forall e c, phi e c -> next all_path (phi' e) c) in H.
    apply rule_holds_weak.
    unfold rule_holds_strict; intros; repeat fwd_clos.
    assumption.

  + (* Exists step *)
    clear -H.
    change (forall e c, phi e c -> next ex_path (phi' e) c) in H.
    apply rule_holds_weak.
    unfold rule_holds_strict; intros; repeat fwd_clos.
    assumption.

  + (* Axiom *)
    repeat fwd_clos.
    apply rule_holds_weak.
    assumption.

  + (* Refl *)
    destruct C;[destruct H|].
    unfold rule_holds_strict; intros; repeat fwd_clos.
    destruct f;assumption.

  + (* Trans *)
    unfold rule_holds_strict; intros.
    assert (rule_holds_strict
               match C with
               | Some _ => true
               | None => false
               end (Rule f phi phi') gamma) by (repeat fwd_clos; assumption).
    clear IHproof1.
    assert (suc_if_nonempty C (always (rule_holds_strict false (Rule f phi' phi''))) gamma).
    apply union_system_split in IHproof2.
    pose proof (valid_impl_always IHproof2 (always_always Hsystem));
      clear IHproof2 Hsystem.
    pose proof (always_suc_if C (always_always H1)); clear H1.
    apply circ_hyp_restate in Hcsystem.
    revert H2 Hcsystem.
    apply suc_if_lift.
    apply always_lift.
    clear.
    unfold Impl. 
    intuition.
    apply H1.
    clear.
    firstorder.
    
    specialize (H0 _ H).
    clear -H0 H1.

    destruct C;simpl in * |- *.
    assert (next f (reach f (reach f (phi'' rho))) gamma).
    revert H1 H0.
    apply next_any_lift.
    apply reach_always_lift.
    clear. intuition.
    clear -H.
    revert H.
    match goal with [|- next _ ?P gamma -> next _ ?Q gamma] =>
       apply next_any_lift with (fun c => P c -> Q c);[trivial|]
    end.
    apply always_any.
    apply valid_always.
    clear.
    intro c.
    apply reach_join.

    apply reach_join.
    revert H1 H0.
    apply reach_always_lift.
    clear. intuition.

+ (* consequence *)
  unfold rule_holds_strict; intros.
  repeat fwd_clos.
  specialize (H9 _ H6).
  revert H9; clear -H0.
  apply (reach_strict_always_lift _ _ _ _ (@MP _ _)).
  apply valid_always.
  unfold valid, Impl. auto.

+ (* case *)
  unfold rule_holds_strict; intros; repeat fwd_clos.
  destruct H; repeat fwd_clos; assumption.

+ (* abstraction *)
  unfold rule_holds_strict; intros; repeat fwd_clos.
  destruct H.
  repeat fwd_clos.
  revert H5.
  clear.
  apply (reach_strict_always_lift _ _ _ _ (@MP _ _)).
  firstorder.

+ (* Circularity *)

  apply rule_holds_weak.
  repeat fwd_clos.
  clear -Hcsystem H.
  unfold cons_opt_system in H.
  simpl system_holds in H.
  assert (always (Impl (anySuccessors (always (rule_holds_strict true (Rule f phi phi'))))
                       (rule_holds_strict true (Rule f phi phi'))) gamma).
  unfold always at 1; unfold Impl; intros.
  apply (H c' H0); clear H.
  assert (anySuccessors (always (system_holds (system_opt C))) c').
     clear -H0 Hcsystem. unfold anySuccessors, always in * |- *.
     intros. assert (clos SF true gamma c'0). eapply clos_cons_rt; eauto using clos.
     rewrite clos_iff_left in H2. inversion H2; subst. firstorder using clos.
     rewrite <- clos_iff_left in H2,H4. eapply Hcsystem. eassumption.
     pose proof (clos_cat H4 H1). auto using clos_unstrict.
  revert  H H1; clear.
  apply anysuc_lift. apply always_lift.
  clear; unfold system_holds; intros.
  destruct H1.
  auto.
  destruct H1.
  subst. rewrite e in H0. assumption.

  fwd_clos.
  clear -H1.
  unfold Impl in H1.
  
  
  destruct f; simpl; intros.
  unfold successors.
  
     SearchAbout clos.
     intuition. eapply Hcsystem. assumpt
  revert Hcsystem H1.
  apply anysuc_lift.
  
  
  assert (anySuccessors (always ) gamma).
  generalize (always_any (always_always H)); clear H.
  revert Hcsystem.
  apply anysuc_lift.
  
  repeat fwd_clos.

  
  (* tidy hypotheses a bit before starting coinduction *)


  destruct f.

+ (* Substitution *)
  unfold rule_holds_strict; intros; repeat fwd_clos.
  assumption.

+ (* Logical framin *)
  unfold rule_holds_strict; intros; repeat fwd_clos.
  destruct H.
  repeat fwd_clos.
  revert H6; clear -H5.
  apply (reach_strict_always_lift _ _ _ _ (@MP _ _)).
  firstorder.
Qed.

End FixBaseSystem.
End domain.
