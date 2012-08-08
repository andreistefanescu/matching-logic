Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
  | H : _ |- _ => try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
  clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
    set (x := name); move_to_top x
  | assert_eq x name; move_to_top x
  | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.
Tactic Notation "SSSSSSSCase" constr(name) := Case_aux SSSSSSSCase name.

Require Import CondsysSequential.
Require Import List.
Print List.

Module MatchLDerived (Base : ObjectLanguage).
  
  Export Base.

  Module ProofSystem := MatchLProofSystem Base.
  Export ProofSystem.
  
  Axiom infiniteV : forall vars, {v : Var | ~In v vars}.
  Axiom stateless_proper : forall phi : Formula,
    (forall gamma gamma' rho, Satisfies gamma rho phi -> Satisfies gamma' rho phi)
    -> stateless phi.

  Axiom lookup : forall X rho, exists gamma,
    UpdateV rho X gamma = rho.
  Axiom notFreeExists : forall X phi,
    notFree X (Exists X phi).

  Definition someVar : Var := projT1 (infiniteV nil).
  Definition trueF : Formula := Exists someVar (Equals (projT1 someVar) (projT1 someVar)).
  Lemma trueF_true : Valid trueF.
  Proof.
    unfold Valid, trueF; intros. rewrite <- SatExists. exists gamma.
    rewrite <- SatEquals. reflexivity.
  Qed.
  Lemma Valid_stateless : forall f, Valid f -> stateless f.
  Proof. auto using stateless_proper. Qed.
  Lemma trueF_stateless : stateless trueF.
  Proof. apply Valid_stateless; apply trueF_true. Qed.
  Hint Resolve trueF_true trueF_stateless : trueF.
  Lemma true_add : forall f, Valid (Implies f (And f trueF)).
  Proof. unfold Valid; intros; rewrite <- SatImplies, <- SatAnd; auto with trueF. Qed.
  Lemma true_drop : forall f, Valid (Implies (And f trueF) f).
  Proof. unfold Valid; intros; rewrite <- SatImplies, <- SatAnd; tauto. Qed.
  Hint Resolve true_add true_drop : trueF.

  Definition Equiv (f f' : Formula) := Valid (Implies f f') /\ Valid (Implies f' f).

  Definition rule_weaker (r r' : SimpleRule) :=
    Valid (Implies (fst r) (fst r')) /\
    Valid (Implies (snd r') (snd r)).
  Lemma rule_weaken : forall A C r', PS A C (fst r') (snd r') ->
     forall r, rule_weaker r r' -> PS A C (fst r) (snd r).
  Proof.
     intros. destruct H0. eauto using ps_conseq.
  Qed.

  Definition rule_frame (r : SimpleRule) psi : SimpleRule
    := (And (fst r) psi, And (snd r) psi).

  Definition sem_subsystem (S S' : SimpleSystem) : Prop :=
    forall r, In r S -> exists r', In r' S' /\ exists psi, stateless psi /\
       rule_weaker r (rule_frame r' psi).

  Definition subsystem (S S' : SimpleSystem) : Prop :=
    forall r, In r S -> In r S'.

  Definition Weakening := forall A C phi phi',
    PS A C phi phi' ->
    forall A' C', subsystem A A' -> subsystem C' C -> subsystem C (union_ssys A' C') ->
      PS A' C' phi phi'.
  Definition SemWeakening := forall A C phi phi',
    PS A C phi phi' ->
    forall A' C', sem_subsystem A A' -> sem_subsystem C (union_ssys A' C') ->
      (C = nil -> C' = nil) -> PS A' C' phi phi'.

  Lemma sub_better : forall (A A' : SimpleSystem),
    subsystem A A' -> sem_subsystem A A'.
  Proof.
    unfold subsystem, sem_subsystem. intros. exists r.
      intuition. exists trueF. split. auto with trueF.
      unfold rule_weaker; simpl; auto with trueF.
  Qed.

  Lemma stongest : SemWeakening -> Weakening.
  Proof.
    unfold SemWeakening, Weakening. intros.
    apply H with A C. assumption.
    specialize (H A C phi phi' H0 A' C').
    apply sub_better; assumption.
    apply sub_better; assumption.
    clear -H2. intro. subst.
      destruct C'. reflexivity.
      destruct (H2 s). left; reflexivity.
  Qed.

  Lemma sub_refl (A : SimpleSystem) : subsystem A A.
  Proof. firstorder. Qed.
  Lemma sub_union (A A' B : SimpleSystem) : subsystem A B -> subsystem A' B ->
    subsystem (union_ssys A A') B.
  Proof. unfold subsystem, union_ssys. intuition. edestruct in_app_or; eauto. Qed.
  Lemma sub_union_l (A B B' : SimpleSystem) : subsystem A B ->
    subsystem A (union_ssys B B').
  Proof. unfold subsystem, union_ssys. intuition. Qed.
  Lemma sub_union_r (A B B' : SimpleSystem) : subsystem A B' ->
    subsystem A (union_ssys B B').
  Proof. unfold subsystem, union_ssys. intuition. Qed.
  Lemma sub_empty (A : SimpleSystem) : subsystem A empty_ssys -> A = empty_ssys.
  Proof. unfold subsystem, empty_ssys. intuition. destruct A. reflexivity.
    destruct (H s). firstorder.
  Qed.
  Lemma sub_cons (A B : SimpleSystem) (phi phi' : Formula) :
    subsystem A B -> subsystem (cons_ssys phi phi' A) (cons_ssys phi phi' B).
  Proof. firstorder. Qed.
  Hint Resolve sub_refl sub_union sub_union_l sub_union_r sub_cons sub_empty : subsystems.

  Lemma weakening : forall A C phi phi',
    PS A C phi phi' ->
    forall A' C', subsystem A A' -> subsystem C' C -> subsystem C (union_ssys A' C') ->
      PS A' C' phi phi'.
  Proof.
    intros A C phi phi' proof.
    induction proof; intros; try econstructor (solve[eauto with subsystems]).
    Case "ps_refl".
    replace C' with empty_ssys by (symmetry; auto with subsystems). constructor.
    Case "ps_circ".
    constructor.
    apply IHproof; auto with subsystems.
    revert H1. clear. unfold subsystem, union_ssys, cons_ssys.
    intuition. destruct H.
      subst; auto with datatypes.
      specialize (H1 _ H); clear H. apply in_app_or in H1.
      destruct H1; auto with datatypes.
  Qed.

  Lemma sunion (A B C : SimpleSystem) :
    sem_subsystem A C -> sem_subsystem B C -> sem_subsystem (union_ssys A B) C.
  Proof. intros; unfold sem_subsystem; intros.
    apply in_app_or in H1.
    destruct H1; auto.
  Qed.
  Lemma sunion_l (A B C : SimpleSystem) :
    sem_subsystem A C -> sem_subsystem A (union_ssys B C).
  Proof. intros; unfold sem_subsystem; intros.
    specialize (H r H0).
    destruct H. exists x. unfold union_ssys; intuition.
  Qed.
  Lemma sunion_r (A B C : SimpleSystem) :
    sem_subsystem A B -> sem_subsystem A (union_ssys B C).
  Proof.  intros; unfold sem_subsystem; intros.
    specialize (H r H0).
    destruct H. exists x. unfold union_ssys; intuition.
  Qed.
  Lemma sunion_refl (A : SimpleSystem) : sem_subsystem A A.
  Proof. intro; intros. exists r. split;auto. exists trueF.
    split. auto with trueF. unfold rule_weaker; simpl; auto with trueF.
  Qed.
  Lemma scons (A B : SimpleSystem) (phi phi' : Formula) :
    sem_subsystem A B -> sem_subsystem (cons_ssys phi phi' A) (cons_ssys phi phi' B).
  Proof. intros; intro; intros.
    destruct H0.
    Case "new".
    exists r. subst; simpl; intuition.
      exists trueF; simpl; intuition. unfold rule_weaker; simpl; auto with trueF.
    Case "old".
      fold (In r A) in H0.
      specialize (H _ H0).
      destruct H. exists x.
      intuition. right; assumption.
  Qed.
  Hint Resolve sunion sunion_l sunion_r sunion_refl scons : subsystems.

  Ltac and_ressoc := unfold Valid; intros; rewrite <- ?SatImplies, <- ?SatAnd; tauto.
  Lemma And_assoc_r : forall (a b c : Formula),
    Valid (Implies (And (And a b) c) (And a (And b c))).
  Proof. and_ressoc. Qed.
  Lemma And_assoc_l : forall (a b c : Formula),
    Valid (Implies (And a (And b c)) (And (And a b) c)).
  Proof. and_ressoc. Qed.
  Lemma And_drop_r : forall (a b : Formula),
    Valid (Implies (And a b) a).
  Proof. and_ressoc. Qed.
  Hint Resolve And_assoc_l And_assoc_r And_drop_r : And_reassoc.

  Lemma stateless_conj : forall f f', stateless f -> stateless f' -> stateless (And f f').
  Proof. intros. apply stateless_proper.
    intros gamma gamma' rho. rewrite <- ? SatAnd.
    intuition eauto using stateless_sat.
  Qed.

  Lemma sweakening : forall A C phi phi',
    PS A C phi phi' ->
    forall A' C', sem_subsystem A A' -> sem_subsystem C C' ->
      (C = nil -> C' = nil) -> PS A' C' phi phi'.
  Proof.
    induction 1; intros;try econstructor solve[eauto with subsystems].
    Case "ps_axiom_A".
    specialize (H1 _ H).
    destruct H1 as [r' [HA'r' [psi' [Hstateless [Hvalid1 Hvalid2 ]]]]].
    eapply ps_conseq. Focus 2. apply ps_axiom_A. eexact HA'r'.
      apply stateless_conj. eexact H0. eexact Hstateless.
    clear -Case Hvalid1. intro; intros. specialize (Hvalid1 gamma rho). revert Hvalid1.
      simpl; rewrite <- ? SatImplies, <- ? SatAnd; intuition.
    clear -Case Hvalid2. intro;intros. specialize (Hvalid2 gamma rho). revert Hvalid2.
      simpl; rewrite <- ? SatImplies, <- ? SatAnd; intuition.
    Case "ps_refl".
      rewrite H1. apply ps_refl. reflexivity.
    Case "ps_circ".
    apply ps_circ. apply IHPS; auto with subsystems.
    intro. discriminate H3.
   Qed.

  Definition frame_system (S : SimpleSystem) (psi : Formula) : SimpleSystem :=
    map (fun r => rule_frame r psi) S.
  Lemma srefl_frame : forall (S : SimpleSystem) (psi : Formula),
    stateless psi -> sem_subsystem (frame_system S psi) S.
  Proof.
    unfold sem_subsystem; intros.
    induction S0. destruct H0.
    destruct H0.
    exists a. split. left;reflexivity. exists psi.
      split;auto. subst. clear. split;
      unfold Valid; intros; rewrite <- SatImplies; tauto.
    specialize (IHS0 H0); clear H0.
    destruct IHS0. exists x.
      intuition.
  Qed.

  Lemma frame1 (A C : SimpleSystem) (phi phi' : Formula) :
    PS A C phi phi' -> forall psi, stateless psi ->
    PS (frame_system A psi) (frame_system C psi) (And phi psi) (And phi' psi).
  Proof.
    induction 1.
    Case "ps_axiom_S".
    intros. eapply ps_conseq; eauto with And_reassoc.
    apply ps_axiom_S. assumption.
    apply stateless_conj; assumption.
    intros. specialize (H2 srule H4 _ H3).
    clear -Case H2. simpl in H2. unfold frame_system, union_ssys in H2. rewrite map_app in H2.
      eauto using ps_conseq with And_reassoc.
    Case "ps_axiom_A".
      rename psi into psi0. intros. eapply ps_conseq.
      Focus 2. apply ps_axiom_A. instantiate (1:=rule_frame srule psi).
        clear -Case H. unfold frame_system. apply in_map with (f:=fun r => rule_frame r psi) in H. exact H.
        eexact H0.
        destruct srule; simpl. and_ressoc. 
        destruct srule; simpl. and_ressoc.
    Case "ps_refl".
        simpl. intros; constructor.
    Case "ps_trans".
        intros; eapply ps_trans; auto.
        specialize (IHPS2 psi H1). 
        unfold frame_system, union_ssys in IHPS2.
        rewrite map_app in IHPS2. assumption.
    Case "ps_conseq".
        intros. specialize (IHPS psi H2).
        eapply ps_conseq;[|eexact IHPS|].
        revert H. unfold Valid. intros. specialize (H gamma rho). revert H.
             rewrite <- ?SatImplies, <- ?SatAnd. tauto.
        revert H1. unfold Valid. intros. specialize (H1 gamma rho). revert H1.
             rewrite <- ?SatImplies, <- ?SatAnd. tauto.
     Case "ps_case".
        intros. specialize (IHPS1 psi H1). specialize (IHPS2 psi H1).
        apply ps_conseq with (Or (And phi1 psi) (And phi2 psi)) (And phi psi).
        clear -Case. unfold Valid. intros.
        repeat progress rewrite <- ?SatImplies, <- ?SatAnd, <- ?SatOr. tauto.
        apply ps_case; assumption. 
        unfold Valid. intros.
        repeat progress rewrite <- ?SatImplies, <- ?SatAnd, <- ?SatOr. tauto.
     Case "ps_abstr".
        intros. specialize (IHPS psi H1).
(*ASSUME*) admit.
     Case "ps_circ".
        intros. specialize (IHPS psi H0).
        apply ps_circ. exact IHPS.
  Qed.

Print Assumptions frame1.

  Lemma frame (A C : SimpleSystem) (phi phi' : Formula) :
    PS A C phi phi' -> forall psi, stateless psi ->
    PS A C (And phi psi) (And phi' psi).
  Proof.
    intros. apply sweakening with (frame_system A psi) (frame_system C psi)
      ; auto using frame1, srefl_frame.
    destruct C; simpl; congruence.
  Qed.

Lemma scoping : forall (A C : SimpleSystem) (X : Var) (phi phi' : Formula),
  PS A C phi phi' -> PS A C (Exists X phi) (Exists X phi').
Proof.
  intros.
  apply ps_abstr.
  apply ps_conseq with (2:=H).
  and_ressoc. 
  unfold Valid. intros.
  rewrite <- SatImplies, <- SatExists.
  intros. destruct (lookup X rho).
  exists x. rewrite H1. assumption.
  apply notFreeExists.
Qed.

  Definition eq_ssys (S1 S2 : SimpleSystem) : Prop :=
    sem_subsystem S1 S2 /\ sem_subsystem S2 S1.
  Lemma restate : forall A C phi phi',
    PS A C phi phi' -> forall A' C',
    eq_ssys A A' -> eq_ssys C C' -> PS A' C' phi phi'.
  Proof.
    unfold eq_ssys; intros; apply sweakening with A C; intuition.
    subst C. destruct C'. reflexivity.
    clear -H5.
    unfold sem_subsystem in H5.
    specialize (H5 s).
    destruct H5. left;reflexivity.
    destruct H as [[]].
  Qed.

  Section Weaken.
  Variable formula_dec : forall (f1 f2 : Formula), {f1=f2}+{f1<>f2}.

  Lemma srule_dec : forall (r1 r2 : SimpleRule), {r1=r2}+{r1<>r2}.
  Proof. decide equality. Qed.

  Definition subtract_ssys (r : SimpleRule) (S : SimpleSystem) : SimpleSystem :=
     remove srule_dec r S.

Lemma remove_app : forall A eq x l1 l2,
  @remove A eq x (l1 ++ l2) = remove eq x l1 ++ remove eq x l2.
Proof.
  induction l1. auto.
  simpl. intro l2; specialize (IHl1 l2).
  destruct (eq x a); simpl; congruence.
Qed.

SearchAbout remove.
Lemma In_remove : forall A eq x x' l, In x (@remove A eq x' l) -> In x l.
Proof.
  intros. induction l.
  destruct H.
  simpl in H.
  destruct (eq x' a).
  right; auto.
  destruct H.
  left; auto.
  right; auto.
Qed.

Lemma remove_other : forall A eq x x' l,
  x <> x' -> In x l -> In x (@remove A eq x' l).
Proof.
  induction l. destruct 2.
  simpl. destruct (eq x' a); destruct 2.
    congruence. auto. left; congruence. right; auto.
Qed.

  Lemma cut : forall A C phi phi' r,
    PS A C phi phi' ->
    PS (subtract_ssys r A) (r :: C) (fst r) (snd r) ->
    PS (subtract_ssys r A) (subtract_ssys r C) phi phi'.
  Proof.
    induction 1; intros Hsubproof; try econstructor (solve[eauto using weakening with subsystems]).
    Case "ps_axiom_S".
    apply ps_axiom_S; try assumption.
    intros srule Hsrule.
    lapply (H2 srule Hsrule). clear H2 Hsrule.
    intro H2. apply (weakening _ _ _ _ H2); auto with subsystems.
    clear -Case. unfold subsystem, subtract_ssys, union_ssys. rewrite remove_app. auto.
    clear -Case Hsubproof. 
    apply (weakening _ _ _ _ Hsubproof); auto with subsystems.
    clear -Case. unfold subsystem, subtract_ssys, union_ssys. rewrite remove_app; auto  with datatypes. 
    clear -Case. unfold subsystem, subtract_ssys, union_ssys.
      intuition. destruct H. left; auto. destruct H.
    clear -Case. unfold subsystem, subtract_ssys, union_ssys.
      intros. destruct (srule_dec r r0). subst; auto with datatypes.
        destruct H. destruct (n H).
      fold (In r0 C) in H. apply in_or_app. left.
        apply remove_other. congruence. apply in_or_app. right; assumption.
    Case "ps_axiom_A".
    destruct (srule_dec r srule).
    SCase "srule = r".
    apply frame. subst. apply ps_circ.
    apply (weakening _ _ _ _ Hsubproof); auto with subsystems.
    unfold subsystem. intro r.
      destruct 1. left; destruct srule; simpl in H1; congruence.
      fold (In r (subtract_ssys srule C)) in H1.
      unfold subtract_ssys in H1.
      apply In_remove in H1. auto with datatypes.
    clear -Case.
    unfold subsystem. intros.
      destruct (srule_dec r srule).
      apply in_or_app. right. left. destruct srule; simpl; congruence.
      destruct H. exfalso; auto.
    fold (In r C) in H. apply in_or_app. right. right.
    apply remove_other; assumption. assumption.
    SCase "r <> srule".
    apply ps_axiom_A; auto. apply remove_other; auto; congruence.
    Case "ps_trans".
    apply ps_trans with phi2;[auto|].
    lapply IHPS2.
    clear -Case.
    intro H. apply (weakening _ _ _ _ H).
    clear -Case. unfold subsystem, subtract_ssys, union_ssys. rewrite remove_app; auto  with datatypes.
    simpl; auto with subsystems.
    unfold subsystem; intros. destruct H0.
    clear -Case Hsubproof.
    apply (weakening _ _ _ _ Hsubproof).
    clear -Case. unfold subsystem, subtract_ssys, union_ssys. rewrite remove_app; auto  with datatypes.
    clear -Case. unfold subsystem, subtract_ssys, union_ssys. simpl; tauto.
    clear -Case. unfold subsystem, subtract_ssys, union_ssys. simpl.
      intros. destruct (srule_dec r r0).
        apply in_or_app. right. left. auto.
        destruct H. destruct (n H).
        apply in_or_app. left. simpl. rewrite remove_app. apply in_or_app.
        right. apply remove_other. congruence. assumption.
    Case "ps_circ".
    destruct (srule_dec r (phi,phi')).
    SCase "r = (phi,phi')".
    subst; clear -SCase Case Hsubproof. simpl in Hsubproof.
    subst. apply ps_circ.
    apply (weakening _ _ _ _ Hsubproof).
    auto with subsystems.
    clear -SCase Case. unfold subsystem, subtract_ssys; intros.
      destruct H. left. assumption.
      fold (In r (remove srule_dec (phi,phi') C)) in H.
      apply In_remove in H. right; assumption.
    clear -SCase Case. unfold subsystem, subtract_ssys, union_ssys; intros.
      destruct (srule_dec r (phi,phi')).
      apply in_or_app. right. left. congruence.
      destruct H. destruct n; congruence.
      fold (In r C) in H.
      apply in_or_app. right. right. apply remove_other; assumption.
    SCase "r <> (phi, phi')".
      apply ps_circ.
      lapply IHPS.
      clear -SCase Case n.
        simpl. destruct (srule_dec r (phi,phi')).
        destruct n;congruence. auto.
      clear -SCase Case n Hsubproof.
      apply (sweakening _ _ _ _ Hsubproof); auto with subsystems.
      unfold sem_subsystem.
      clear -SCase Case n. intros.
      exists r0. split.
         destruct H; simpl; auto with datatypes.
         exists trueF. split. auto with trueF.
         split; simpl; auto with trueF.
         discriminate.
   Qed.
End MatchLDerived.