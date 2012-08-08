Require Import ProofSystem.
Require Import Reachability.
Require Import Closure.
Require Import List.

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

Module Type Soundness (Export Base : ObjectLanguage)
  (Export BaseR : Reachability Base)
  (Export BaseP : ProofSystem Base BaseR).

  Export BaseP.
  
  Definition GStronglyValid (strict : bool) (srule : SimpleRule) g : Prop :=
      forall gamma,
        g SuccEq gamma ->
        forall rho,
          Satisfies gamma rho (fst srule) ->
          exists gamma',
            GoesTo strict gamma gamma' /\
            Satisfies gamma' rho (snd srule).

  Definition GStronglyValidssys (strict : bool) (ssys : SimpleSystem) g : Prop :=
    List.Forall (fun srule => GStronglyValid strict srule g) ssys.

  Lemma GStronglyValidUnstrict :
    forall g srule,
      GStronglyValid true srule g ->
      GStronglyValid false srule g.
    intros g srule.
    unfold GStronglyValid.
    intros H gamma gSuccEqgamma rho Hsat.
    specialize (H gamma gSuccEqgamma rho Hsat).
    elim H; intros gamma' Htemp; decompose [and] Htemp; clear Htemp.
    exists gamma'; split ; [apply clos_unstrict; auto | auto].
  Qed.
  
  Lemma GoesToImpliesSuccEq :
    forall gamma gamma' strict,
      GoesTo strict gamma gamma' ->
      gamma SuccEq gamma'.
    intros gamma gamma' strict HGoesTo.

    induction HGoesTo.
    apply clos_refl.
    apply clos_step.

    unfold TerminationDependence.
    left.
    apply clos_step.
    assumption.
    eapply clos_trans; eauto.
  Qed.

  Lemma GoesToImpliesSucc :
    forall gamma gamma',
      GoesTo true gamma gamma' ->
      clos _ (TerminationDependence S) true gamma gamma'.
    intros gamma gamma' HGoesTo.

    induction HGoesTo.
    apply clos_refl.
    apply clos_step.

    unfold TerminationDependence.
    left.
    apply clos_step.
    assumption.
    eapply clos_trans; eauto.
  Qed.

  Tactic Notation "splitAnd" ident(H) ident(name1) ident(name2) :=
    match type of H with
      ?P /\ ?Q =>
      assert (name1: P) by (apply H); assert(name2: Q) by (apply H); clear H
    end.
  
  Lemma gammaStronglyValidTrans : forall phi1 phi2 phi3 g s1 s2 s3,
    GStronglyValid s1 (phi1, phi2) g ->
    GStronglyValid s2 (phi2, phi3) g ->
    s3 = orb s1 s2 ->
    GStronglyValid s3 (phi1, phi3) g.
    intros phi1 phi2 phi3 g s1 s2 s3 H1 H2.
    unfold GStronglyValid in *.

    intros Hstrict gamma HgSuccEqgamma rho Hsat.
    specialize (H1 gamma HgSuccEqgamma rho Hsat).

    elim H1; intros gamma' Htemp; splitAnd Htemp HGoesTo Hsat'; clear H1.

    assert (HgSuccEqgamma' : g SuccEq gamma').
    eapply clos_trans.
    eauto.
    eapply GoesToImpliesSuccEq.
    eauto.

    specialize (H2 gamma' HgSuccEqgamma' rho Hsat').
    
    elim H2; intros gamma'' Htemp; splitAnd Htemp HGoesTo' Hsat''; clear H2.
    
    exists gamma''; split.
    eapply clos_cat''; eauto.
    destruct s1, s2, s3; compute; tauto.
    exact Hsat''.
  Qed.
  
  Lemma sound_union :
    forall g A B s1 s2 s3,
      GStronglyValidssys s1 A g ->
      GStronglyValidssys s2 B g ->
      s3 = andb s1 s2 ->
      GStronglyValidssys s3 (ssysUnion A B) g.
    intros g A B s1 s2 s3 H1 H2 Hstrict.
    unfold GStronglyValidssys in *.
    unfold ssysUnion.

    rewrite List.Forall_forall in *.
    intros x Hin.

    case (List.in_app_or A B x Hin);
      destruct s3, s2, s1;
        intros;
          try inversion Hstrict;
            try auto;
              try apply GStronglyValidUnstrict; try auto.
  Qed.
    
  Definition GAlmostStronglyValidssys (strict : bool) (C : SimpleSystem) g :=
    forall gnext,
      clos M (TerminationDependence S) true g gnext ->
      GStronglyValidssys strict C gnext.

  Definition inCS_ (x : CondRule) (y : CondSystem) := y x.

  Notation "x 'inCS' y" := (inCS_ x y) (at level 60).

  Lemma TerminatesWeaken : forall gamma gamma',
    Terminates S gamma ->
    gamma SuccEq gamma' ->
    Terminates S gamma'.
  Proof.
    intros.
    induction H0.
    assumption.
    apply H. unfold Prec. apply clos_step. auto.
    auto.
  Qed.
  
  Lemma GStronglyValidWeaken : forall strict g gnext phi phi',
    GStronglyValid strict (phi, phi') g ->
    g SuccEq gnext ->
    GStronglyValid strict (phi, phi') gnext.
  Proof.
    induction 2.

    assumption.

    unfold GStronglyValid in *.
    intros gamma HbSuccEqgamma rho Hsat.
    assert (HaSuccEqgamma : a SuccEq gamma).
    eapply clos_trans_lt.
    constructor 2. apply H0.
    apply HbSuccEqgamma.
    specialize (H gamma HaSuccEqgamma rho Hsat).
    exact H.

    auto.
  Qed.

  Lemma GStronglyValidssysWeaken : forall strict g gnext ssys,
    GStronglyValidssys strict ssys g ->
    g SuccEq gnext ->
    GStronglyValidssys strict ssys gnext.
  Proof.
    unfold GStronglyValidssys.
    intros.
    rewrite Forall_forall in *.
    intros.
    eapply GStronglyValidWeaken.
    apply H.
    destruct x.
    apply H1.
    apply H0.
  Qed.

  Lemma trans_help : forall M (R : Relation_Definitions.relation M) a b c,
    clos M R false b c ->
    clos M R true a b ->
    clos M R true a c.
  Proof.
    intros.
    eapply clos_cons_lt.
    apply H0.
    apply H.
  Qed.

  Lemma trans_help' : forall M (R : Relation_Definitions.relation M) a b c,
    clos M R true b c ->
    clos M R false a b ->
    clos M R true a c.
  Proof.
    intros.
    eapply clos_cons_rt.
    apply H0.
    apply H.
  Qed.

  Lemma GAlmostStronglyValidssysWeaken : forall strict g gnext ssys,
    GAlmostStronglyValidssys strict ssys g ->
    g SuccEq gnext ->
    GAlmostStronglyValidssys strict ssys gnext.
  Proof.
    unfold GAlmostStronglyValidssys.
    intros.
    eapply GStronglyValidssysWeaken.
    apply H.
    eapply trans_help'.
    apply H1.
    apply H0.
    apply clos_refl.
  Qed.

  Lemma GStronglyValidWeaken' : forall strict gamma gamma0 phi phi',
    GStronglyValid strict (phi, phi') gamma ->
    gamma SuccEq gamma0 ->
    GStronglyValid strict (phi, phi') gamma0.
  Proof.
    induction 2.
    assumption.
    eapply GStronglyValidWeaken. apply H. apply clos_step. assumption.
    apply IHclos2. apply IHclos1. assumption.
  Qed.
  
  Lemma sound_unstrict :
    forall phi phi' gamma,
      GStronglyValid true (phi, phi') gamma ->
      GStronglyValid false (phi, phi') gamma.
    intros.
    unfold GStronglyValid in *.
    intros.
    specialize (H gamma0 H0 rho H1).
    elim H; intros.
    exists x.
    split.
    apply clos_unstrict.
    apply H2.
    apply H2.
  Qed.

  Lemma SuffixWeaken : forall { A : Type },
    forall (slist blist : list A),
      forall (shead : A),
        (shead :: slist) SuffixOf blist ->
        slist SuffixOf blist.
    intros.
    remember (cons shead slist) as slist'.
    induction H.
    rewrite Heqslist'.
    repeat constructor.
    constructor 2.
    apply IHIsSuffix.
    assumption.
  Qed.

  Lemma SuffixOfImpliesIn : forall { A : Type },
    forall (first : A) rest list,
      (first :: rest) SuffixOf list ->
      List.In first list.
    intros.
    remember (cons first rest) as flist.
    induction H.
    subst slist.
    constructor.
    reflexivity.
    constructor 2.
    apply IHIsSuffix.
    apply Heqflist.
  Qed.

  Lemma AndImplies :
    forall P Q R : Prop,
      ((P /\ Q) -> R) <->
      (P -> (Q -> R)).
    intros.
    split; intros.
    apply H.
    constructor; assumption.
    apply H; apply H0.
  Qed.

  Lemma ExistsList :
    forall R list,
      (forall elem,
        List.In elem list ->
        exists elem',
          R elem elem') ->
      (exists list',
        InTSList R list list').
    intros.
    induction list.
    exists nil; constructor.

    elim IHlist; intros.
    elim (H a); intros.
    exists (x0 :: x).
    constructor; assumption.
    constructor; reflexivity.
    apply H.
    constructor 2; assumption.
  Qed.

  Lemma SatisfiesListIn : forall gamma gammaList rho list,
    SatisfiesList gammaList rho (mapFst list) ->
    In gamma gammaList ->
    (exists srule,
      In srule list /\ Satisfies gamma rho (fst srule)).
    induction gammaList.
    intros.
    inversion H0.
    intros.
    destruct list.
    inversion H.
    inversion H.
    specialize (IHgammaList rho list H7).
    destruct H0.
    exists s.
    constructor.
    constructor.
    reflexivity.
    subst a.
    subst gamma.
    assumption.
    specialize (IHgammaList H0).
    elim IHgammaList; intros.
    exists x.
    constructor.
    constructor 2.
    apply H8.
    apply H8.
  Qed.

  Lemma InProjectFst : forall x l,
    In x l ->
    In (fst x) (mapFst l).
    intros.
    induction l.
    inversion H.
    inversion H.
    subst a.
    constructor.
    reflexivity.
    specialize (IHl H0).
    constructor 2.
    apply IHl.
  Qed.

  Lemma SuffixHeadIn : forall x : SimpleRule, forall l l',
    (x :: l) SuffixOf l' ->
    In x l'.
    intros.
    remember (x :: l) as l0.
    induction H.
    subst. constructor. reflexivity.
    constructor 2. apply IHIsSuffix. assumption.
  Qed.

  Lemma SatisfiesListInSatisfies : forall gammaList rho s side elem,
    SatisfiesList gammaList rho (mapFst (s :: side)) ->
    In elem gammaList ->
    exists srule : SimpleRule,
      In srule (s :: side) /\ Satisfies elem rho (fst srule).
  Proof.
    intros.
    generalize dependent gammaList.
    generalize dependent s.
    induction side.

    intros.
    inversion H.
    subst phiTail.
    inversion H6.
    subst.
    inversion H0.
    subst.
    exists s.
    split.
    constructor.
    reflexivity.
    assumption.
    contradiction.

    intros.
    inversion H.
    subst.
    inversion H0.
    subst.
    exists s.
    split.
    constructor.
    reflexivity.
    assumption.
    
    specialize (IHside a gammaTail H6 H1).
    elim IHside; intros.
    exists x.
    split.
    constructor 2.
    apply H2.
    apply H2.
  Qed.

  Theorem soundness :
    WeaklyWDSystem S ->
    forall A C phi phi',
      PS A C phi phi' ->
      forall g,
        Terminates S g ->
        GStronglyValidssys true A g ->
        GAlmostStronglyValidssys true C g ->
        ((IsEmpty C ->
          GStronglyValid false (phi, phi') g) /\
        ((not (IsEmpty C)) ->
          GStronglyValid true (phi, phi') g)).
  Proof.
    induction 2.
    
    Case "Axiom S".

    destruct crule as [ (phi, phi') side ].
    simpl in *.
  
    intros g HT HA HC.
    
    split; intro Hempty.
    
    SCase "empty circularities".
    clear H2.
    inversion Hempty.
    subst C.
    clear Hempty.

    unfold GStronglyValid.
    intros gamma HgSuccEqgamma rho Hsat.
    simpl in *.

    assert (Hsideh : forall side', side' SuffixOf side ->
      List.Forall (fun srule => RhoStronglyValid rho srule) side').
    induction side'.
    intros.
    constructor.

    intros Hside'.
    rewrite Forall_forall.
    intros x Hx.
    destruct Hx.
    subst a.
    unfold RhoStronglyValid.
    intros.
    
    assert (Hgamma0 : Satisfies gamma0 rho (And (fst x) psi)).
    rewrite <- SatAnd in *.
    split.
    assumption.
    eapply structureless_sat.
    assumption.
    apply Hsat.
    
    assert (Hsucc : gamma Succ gamma0).
    unfold TerminationDependence.
    right.
    exists (phi, phi', side).
    split.
    assumption.
    exists rho.
    exists side'.
    exists x.
    simpl.
    split.
    assumption.
    split.
    rewrite <- SatAnd in Hsat.
    apply Hsat.
    split.
    apply IHside'.
    eapply SuffixWeaken.
    apply Hside'.
    rewrite <- SatAnd in Hgamma0.
    apply Hgamma0.
    
    assert (Hsv : (IsEmpty ssysEmpty ->
        GStronglyValid false (And (fst x) psi, snd x) gamma0)).
    apply H3.
    eapply SuffixOfImpliesIn.
    apply Hside'.
    eapply TerminatesWeaken.
    apply HT.
    eapply clos_trans.
    apply HgSuccEqgamma.
    apply clos_step.
    assumption.

    unfold ssysUnion.
    rewrite app_nil_r.
    eapply GStronglyValidssysWeaken.
    apply HA.
    eapply clos_trans.
    apply HgSuccEqgamma.
    apply clos_step.
    assumption.
    constructor.
    
    assert (Htemp : IsEmpty ssysEmpty).
    constructor.
    specialize (Hsv Htemp).
    clear Htemp.
    unfold GStronglyValid in Hsv.
    specialize (Hsv gamma0 (clos_refl _ _ _) rho Hgamma0).
    elim Hsv. intros gamma1 Hand.
    exists gamma1. apply Hand.

    assert (Hside'side : side' SuffixOf side).
    eapply SuffixWeaken.
    apply Hside'.
    specialize (IHside' Hside'side).
    clear Hside'side.
    rewrite Forall_forall in IHside'.
    apply IHside'.
    apply H2.
    
    assert (HWD : WeaklyWD (phi, phi', side)) by (apply H; apply H0).

    clear H.
    unfold WeaklyWD in *.
    unfold WeaklyWDPattern in *.

    simpl in *.
    splitAnd HWD Hsat' Hside. simpl in *.
    specialize (Hsat' rho).
    elim Hsat'; intros gamma' Htemp; clear Hsat'; rename Htemp into Hsat'.
    exists gamma'.
    split.

    unfold GoesTo.
    apply clos_step.
    eapply TSIntro.
    apply H0.
    simpl.
    rewrite <- SatAnd in Hsat; apply Hsat.
    simpl.
    assumption.
    simpl.
    intros.
    
    destruct side.
    inversion H.
    exists nil.
    constructor.

    specialize (Hsideh (s :: side) (here _)).
    rewrite Forall_forall in Hsideh.
    apply ExistsList.
    intros.
    assert (Hin : exists srule,
        (In srule (s :: side) /\ Satisfies elem rho (fst srule))).
    eapply SatisfiesListInSatisfies.
    apply H.
    assumption.

    elim Hin. intros. clear Hin.
    specialize (Hsideh x). specialize (Hsideh (proj1 H4)).
    unfold RhoStronglyValid in Hsideh.
    specialize (Hsideh elem (proj2 H4)).
    simpl in *.
    elim Hsideh; intros.
    exists x0.
    apply H5.

    rewrite <- SatAnd in *.
    split.
    apply Hsat'.
    eapply structureless_sat.
    apply H1.
    apply Hsat.

    SCase "non-empty circularities".
    clear H2.

    unfold GStronglyValid.
    intros gamma HgSuccEqgamma rho Hsat.
    simpl in *.

    assert (Hsideh : forall side', side' SuffixOf side ->
      List.Forall (fun srule => RhoStronglyValid rho srule) side').
    induction side'.
    intros.
    constructor.

    intros Hside'.
    rewrite Forall_forall.
    intros x Hx.
    destruct Hx.
    subst a.
    unfold RhoStronglyValid.
    intros.
    
    assert (Hgamma0 : Satisfies gamma0 rho (And (fst x) psi)).
    rewrite <- SatAnd in *.
    split.
    assumption.
    eapply structureless_sat.
    assumption.
    apply Hsat.
    
    assert (Hsucc : gamma Succ gamma0).
    unfold TerminationDependence.
    right.
    exists (phi, phi', side).
    split.
    assumption.
    exists rho.
    exists side'.
    exists x.
    simpl.
    split.
    assumption.
    split.
    rewrite <- SatAnd in Hsat.
    apply Hsat.
    split.
    apply IHside'.
    eapply SuffixWeaken.
    apply Hside'.
    rewrite <- SatAnd in Hgamma0.
    apply Hgamma0.
    
    assert (Hsv : (IsEmpty ssysEmpty ->
        GStronglyValid false (And (fst x) psi, snd x) gamma0)).
    apply H3.
    eapply SuffixOfImpliesIn.
    apply Hside'.
    eapply TerminatesWeaken.
    apply HT.
    eapply clos_trans.
    apply HgSuccEqgamma.
    apply clos_step.
    assumption.

    eapply sound_union.
    eapply GStronglyValidssysWeaken.
    apply HA.
    eapply clos_trans.
    apply HgSuccEqgamma.
    apply clos_step.
    assumption.
    apply HC.
    eapply trans_help'.
    apply clos_step.
    apply Hsucc.
    apply HgSuccEqgamma.
    reflexivity.

    constructor.
    
    assert (Htemp : IsEmpty ssysEmpty).
    constructor.
    specialize (Hsv Htemp).
    clear Htemp.
    unfold GStronglyValid in Hsv.
    specialize (Hsv gamma0 (clos_refl _ _ _) rho Hgamma0).
    elim Hsv. intros gamma1 Hand.
    exists gamma1. apply Hand.

    assert (Hside'side : side' SuffixOf side).
    eapply SuffixWeaken.
    apply Hside'.
    specialize (IHside' Hside'side).
    clear Hside'side.
    rewrite Forall_forall in IHside'.
    apply IHside'.
    apply H2.
    
    assert (HWD : WeaklyWD (phi, phi', side)) by (apply H; apply H0).

    clear H.
    unfold WeaklyWD in *.
    unfold WeaklyWDPattern in *.

    simpl in *.
    splitAnd HWD Hsat' Hside. simpl in *.
    specialize (Hsat' rho).
    elim Hsat'; intros gamma' Htemp; clear Hsat'; rename Htemp into Hsat'.
    exists gamma'.
    split.

    unfold GoesTo.
    apply clos_step.
    eapply TSIntro.
    apply H0.
    simpl.
    rewrite <- SatAnd in Hsat; apply Hsat.
    simpl.
    assumption.
    simpl.
    intros.
    
    destruct side.
    inversion H.
    exists nil.
    constructor.

    specialize (Hsideh (s :: side) (here _)).
    rewrite Forall_forall in Hsideh.
    apply ExistsList.
    intros.
    assert (Hin : exists srule,
        (In srule (s :: side) /\ Satisfies elem rho (fst srule))).
    eapply SatisfiesListInSatisfies.
    apply H.
    assumption.

    elim Hin. intros. clear Hin.
    specialize (Hsideh x). specialize (Hsideh (proj1 H4)).
    unfold RhoStronglyValid in Hsideh.
    specialize (Hsideh elem (proj2 H4)).
    simpl in *.
    elim Hsideh; intros.
    exists x0.
    apply H5.

    rewrite <- SatAnd in *.
    split.
    apply Hsat'.
    eapply structureless_sat.
    apply H1.
    apply Hsat.

  Case "Axiom A".

  intros; split; intro HemptyC.
  unfold GStronglyValid; simpl; intros gamma' Hless rho Hsat'.
  assert (Hsrule : GStronglyValid true srule g).
  unfold GStronglyValidssys in H3.
  rewrite Forall_forall in H3.
  apply H3.
  assumption.
  rewrite <- SatAnd in Hsat'; decompose [and] Hsat';
  unfold GStronglyValid in Hsrule.
  specialize (Hsrule gamma' Hless rho H5).
  elim Hsrule; intros gamma''; intros; decompose [and] H6;
    exists gamma''; split.
  try apply clos_unstrict. apply H7.
  apply SatAnd; split.
  apply H7. eapply structureless_sat. assumption. apply H6.
  unfold GStronglyValid; simpl; intros gamma' Hless rho Hsat'.
  assert (Hsrule : GStronglyValid true srule g).
  unfold GStronglyValidssys in H3.
  rewrite Forall_forall in H3.
  apply H3.
  assumption.
  rewrite <- SatAnd in Hsat'; decompose [and] Hsat';
  unfold GStronglyValid in Hsrule.
  specialize (Hsrule gamma' Hless rho H5).
  elim Hsrule; intros gamma''; intros; decompose [and] H6;
    exists gamma''; split.
  try apply clos_unstrict. apply H7.
  apply SatAnd; split.
  apply H7. eapply structureless_sat. assumption. apply H6.
  
  Case "Reflexivity".
  intros. split; intros HemptyC.
  
  SCase "C is empty".
  unfold GStronglyValid; simpl; intros; exists gamma; split ; [ apply clos_refl | assumption ].
  
  SCase "C is not empty".
  unfold IsEmpty in HemptyC. unfold ssysEmpty in HemptyC.
  assert (forall rule : SimpleRule, List.In rule nil -> False).
  apply List.in_nil.
  tauto.
  
  Case "Transitivity".
  intros gamma HT HA HC; split; intros HemptyC.
  
  SCase "C is empty".
  
  specialize (IHPS1 gamma HT HA HC).
  specialize (IHPS2 gamma HT).
  
  assert (HA' : GStronglyValidssys true (ssysUnion A C) gamma).
  eapply sound_union. apply HA.
  unfold GStronglyValidssys. inversion HemptyC. subst C. constructor.
  reflexivity.
  
  assert (HC' : GAlmostStronglyValidssys true ssysEmpty gamma).
  unfold GAlmostStronglyValidssys; unfold ssysEmpty. intros.
  constructor.

  specialize (IHPS2 HA' HC').
  decompose [and] IHPS1. decompose [and] IHPS2.
  eapply gammaStronglyValidTrans. apply H0. assumption. apply H2.
  unfold IsEmpty. unfold ssysEmpty. tauto.
  compute. reflexivity.
  
  SCase "C is not empty".
  specialize (IHPS1 gamma HT HA HC).
  unfold GStronglyValid.
  intros gamma1 Htransition rho Hsat.
  decompose [and] IHPS1.
  clear H0.
  clear IHPS1.
  rename H1 into Hind1.
  specialize (Hind1 HemptyC).
  unfold GStronglyValid in Hind1.
  specialize (Hind1 gamma1 Htransition rho Hsat).
  elim Hind1; intros gamma2; intros.
  decompose [and] H0.
  clear H0.
  rename H1 into Htrans2.
  rename H2 into Hsat2.
  specialize (IHPS2 gamma2).
  
  assert (HT2 : Terminates S gamma2).
  eapply TerminatesWeaken.
  apply HT.
  eapply clos_trans.
  apply Htransition.
  eapply GoesToImpliesSuccEq.
  apply Htrans2.
  specialize (IHPS2 HT2).
  
  assert (Hsound2 : GStronglyValidssys true (ssysUnion A C) gamma2).
  eapply sound_union.
  SSCase "sound w.r.t. A".
  unfold GStronglyValidssys.
  rewrite Forall_forall.
  intros.
  eapply GStronglyValidWeaken'.
  unfold GStronglyValidssys in HA.
  rewrite Forall_forall in HA.
  apply HA.
  destruct x; simpl; apply H0.
  eapply clos_trans.
  apply Htransition.
  eapply GoesToImpliesSuccEq.
  apply Htrans2.
  
  SSCase "sound w.r.t. C".
  unfold GAlmostStronglyValidssys in HC.
  apply HC.
  eapply trans_help'.
  unfold GoesTo in Htrans2.
  eapply GoesToImpliesSucc.
  apply Htrans2.
  assumption.
  reflexivity.
  specialize (IHPS2 Hsound2).
  
  assert (Hemptysound : GAlmostStronglyValidssys true ssysEmpty gamma2).
  unfold GAlmostStronglyValidssys.
  unfold ssysEmpty.
  intros.
  unfold GStronglyValidssys.
  constructor.

  specialize (IHPS2 Hemptysound).
  decompose [and] IHPS2.
  clear H1.
  clear IHPS2.
  rename H0 into Hind2.
  
  assert (Hemptyempty : IsEmpty ssysEmpty).
  constructor.
  specialize (Hind2 Hemptyempty).
  
  unfold GStronglyValid in Hind2.
  simpl in Hind2.
  simpl.
  specialize (Hind2 gamma2).
  specialize (Hind2 (clos_refl _ _ _)).
  specialize (Hind2 rho).
  specialize (Hind2 Hsat2).
  elim Hind2. intros gamma3. intros Hand.
  decompose [and] Hand.
  exists gamma3.
  split.
  eapply clos_cat''.
  apply Htrans2.
  apply H0.
  compute. right. reflexivity.
  assumption.
  
  Case "Consequence".
  rename H0 into V1.
  rename H2 into V2.
  intros gamma HT HA HC.
  specialize (IHPS gamma HT HA HC).
  decompose [and] IHPS.
  rename H0 into HeC.
  rename H2 into HneC.
  split; intro Hemptyness.
  
  SCase "C is empty".
  specialize (HeC Hemptyness).
  unfold GStronglyValid.
  intros gamma' Htrans rho Hsat.
  unfold Valid in V1.
  specialize (V1 gamma' rho).
  rewrite <- SatImplies in V1.
  specialize (V1 Hsat).
  unfold GStronglyValid in HeC.
  specialize (HeC gamma' Htrans rho V1).
  elim HeC; intros gamma'' Hand.
  decompose [and] Hand; clear Hand; rename H into Htrans';
    rename H2 into Hsat'.
  unfold Valid in V2.
  specialize (V2 gamma'' rho).
  rewrite <- SatImplies in V2.
  specialize (V2 Hsat').
  exists gamma''.
  split; assumption.
  
  SCase "C not empty".
  specialize (HneC Hemptyness).
  unfold GStronglyValid.
  intros gamma' Htrans rho Hsat.
  unfold Valid in V1.
  specialize (V1 gamma' rho).
  rewrite <- SatImplies in V1.
  specialize (V1 Hsat).
  unfold GStronglyValid in HeC.
  specialize (HneC gamma' Htrans rho V1).
  elim HneC; intros gamma'' Hand.
  decompose [and] Hand; clear Hand; rename H into Htrans';
    rename H2 into Hsat'.
  unfold Valid in V2.
  specialize (V2 gamma'' rho).
  rewrite <- SatImplies in V2.
  specialize (V2 Hsat').
  exists gamma''.
  split; assumption.
  
  Case "Case analysis".
  intros gamma HT HA HC.
  specialize (IHPS1 gamma HT HA HC).
  specialize (IHPS2 gamma HT HA HC).
  decompose [and] IHPS1.
  decompose [and] IHPS2.
  clear IHPS1.
  clear IHPS2.
  rename H0 into He1.
  rename H1 into Hne1.
  rename H2 into He2.
  rename H3 into Hne2.
  split.
  SCase "empty C".
  intros Hempty.
  specialize (He1 Hempty).
  specialize (He2 Hempty).
  unfold GStronglyValid.
  intros gamma' Htrans rho Hsat.
  simpl in Hsat.
  rewrite <- SatOr in Hsat.
  destruct Hsat.
  unfold GStronglyValid in He1.
  specialize (He1 gamma' Htrans rho H0).
  elim He1; intros gamma'' Hand.
  decompose [and] Hand.
  exists gamma'' ; split; assumption.
  unfold GStronglyValid in He1.
  specialize (He2 gamma' Htrans rho H0).
  elim He2; intros gamma'' Hand.
  decompose [and] Hand.
  exists gamma'' ; split; assumption.
  
  SCase "not empty C".
  intros Hempty.
  specialize (Hne1 Hempty).
  specialize (Hne2 Hempty).
  unfold GStronglyValid.
  intros gamma' Htrans rho Hsat.
  simpl in Hsat.
  rewrite <- SatOr in Hsat.
  destruct Hsat.
  unfold GStronglyValid in He1.
  specialize (Hne1 gamma' Htrans rho H0).
  elim Hne1; intros gamma'' Hand.
  decompose [and] Hand.
  exists gamma'' ; split; assumption.
  unfold GStronglyValid in He1.
  specialize (Hne2 gamma' Htrans rho H0).
  elim Hne2; intros gamma'' Hand.
  decompose [and] Hand.
  exists gamma'' ; split; assumption.
  
  Case "abstraction".
  intros gamma HT HA HC; split; intros Hempty.
  SCase "empty C".
  unfold GStronglyValid.
  intros gamma' Htrans rho Hsat.
  simpl in Hsat.
  rewrite <- SatExists in Hsat.
  elim Hsat; intros gamma0 Hsat0.
  specialize (IHPS gamma HT HA HC).
  decompose [and] IHPS.
  specialize (H2 Hempty).
  unfold GStronglyValid in H1.
  specialize (H2 gamma' Htrans (UpdateV rho X gamma0) Hsat0).
  elim H2; intros gamma'' Hand.
  decompose [and] Hand.
  exists gamma''.
  split. assumption. simpl. simpl in H5.
  rewrite notFree_sat. apply H5. assumption.
  
  SCase "not empty C".
  unfold GStronglyValid.
  intros gamma' Htrans rho Hsat.
  simpl in Hsat.
  rewrite <- SatExists in Hsat.
  elim Hsat; intros gamma0 Hsat0.
  specialize (IHPS gamma HT HA HC).
  decompose [and] IHPS.
  specialize (H3 Hempty).
  unfold GStronglyValid in H1.
  specialize (H3 gamma' Htrans (UpdateV rho X gamma0) Hsat0).
  elim H3; intros gamma'' Hand.
  decompose [and] Hand.
  exists gamma''.
  split. assumption. simpl. simpl in H5.
  rewrite notFree_sat. apply H5. assumption.
  
  Case "Circularity".
  assert (forall gamma : M,
    Terminates S gamma ->
    GStronglyValidssys true A gamma ->
    GAlmostStronglyValidssys true C gamma ->
    GStronglyValid true (phi, phi') gamma).
  induction 1.
  rename x into gamma.
  assert (Terminates S gamma).
  unfold Terminates.
  constructor; assumption.
  intros HA HC.
  
  specialize (IHPS gamma H3 HA).
  
  assert (Htoprove : GAlmostStronglyValidssys true (ssysCons phi phi' C) gamma).
  unfold GAlmostStronglyValidssys.
  unfold ssysCons.
  intros.
  unfold GStronglyValidssys.
  rewrite Forall_forall.
  intros.
  destruct (List.in_inv H5).
  destruct H6.
  apply H2.
  assumption.
  unfold GStronglyValidssys; rewrite Forall_forall; intros.
  eapply GStronglyValidWeaken'.
  destruct x.
  unfold GStronglyValidssys in HA.
  rewrite Forall_forall in HA.
  apply HA.
  assumption.
  apply clos_unstrict.
  assumption.
  unfold GAlmostStronglyValidssys.
  intros.
  unfold GStronglyValidssys.
  rewrite Forall_forall.
  intros.
  unfold GAlmostStronglyValidssys in HC.
  unfold GStronglyValidssys in HC.
  specialize (HC gnext0 (clos_trans _ _ _ _ _ _ H4 H6)).
  rewrite Forall_forall in HC.
  apply HC.
  assumption.
  unfold GAlmostStronglyValidssys in HC.
  unfold GStronglyValidssys in HC.
  specialize (HC gnext H4).
  rewrite Forall_forall in HC.
  apply HC.
  assumption.
  
  specialize (IHPS Htoprove).
  decompose [and] IHPS.
  clear IHPS.
  clear H3.
  
  assert (Htoprove2 :  ~ IsEmpty (ssysCons phi phi' C)).
  unfold IsEmpty.
  unfold ssysCons.
  unfold not.
  intros.
  inversion H3.
  
  specialize (H5 Htoprove2).
  assumption.
  
  intros.
  split.
  intros.
  specialize (H1 g H2 H3 H4).
  apply sound_unstrict.
  intros.
  apply H1; assumption.
  intros.
  apply H1; assumption.

Qed.

End Soundness.