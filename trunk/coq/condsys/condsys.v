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

Module Type Terms.

  Parameter T : Set.
  Parameter IsVariable : T -> Prop.

  Definition Var : Set := { x : T & (IsVariable x) }.

  Parameter Substitution : Set.
  Parameter identity : Substitution.
  Parameter Apply : Substitution -> T -> T.

  Hypothesis identity_refl : forall t, (Apply identity t) = t.
  Parameter Update : Substitution -> Var -> T -> Substitution.

End Terms.

Module Type Formulas (Export Base : Terms).

  Parameter Formula : Set.

  Parameter Equals : T -> T -> Formula.
  Parameter And : Formula -> Formula -> Formula.
  Parameter Or : Formula -> Formula -> Formula.
  Parameter Implies : Formula -> Formula -> Formula.
  Parameter Exists : Var -> Formula -> Formula.
  Parameter Pattern : T -> Formula.

  Parameter ApplyF : Substitution -> Formula -> Formula.

  Parameter notFree : Var -> Formula -> Prop.

  Parameter stateless : Formula -> Prop.

End Formulas.

Module Type Model (Export Base : Terms).

  Parameter M : Set.

  Parameter Valuation : Set.

  Parameter value : Valuation -> T -> option M.

  Parameter UpdateV : Valuation -> Var -> M -> Valuation.

  Parameter ApplyV : Substitution -> Valuation -> Valuation.

End Model.

Module Type Satisfaction (Export Base : Terms)
  (Export BaseM : Model Base)
  (Export BaseF : Formulas Base).

  Parameter Satisfies : M -> Valuation -> Formula -> Prop.

  Axiom SatApply : forall rho phi subst gamma,
    Satisfies gamma rho (ApplyF subst phi) <->
    Satisfies gamma (ApplyV subst rho) phi.

  Axiom stateless_sat : forall phi, stateless phi ->
    forall gamma gamma' rho,
      Satisfies gamma rho phi ->
      Satisfies gamma' rho phi.

  Axiom notFree_sat : forall x phi,
    notFree x phi ->
    forall gamma rho t,
      Satisfies gamma rho phi <->
      Satisfies gamma (UpdateV rho x t) phi.

  Definition Valid phi :=
    forall gamma rho,
      Satisfies gamma rho phi.

Print option.

(*
    value rho t = value rho t'
    <->
    Satisfies gamma rho (Equals t t').
*)
  Axiom SatEquals : forall rho t t' gamma,
    value rho t = value rho t'
    <->
    Satisfies gamma rho (Equals t t').

  Axiom SatExists : forall rho x phi gamma,
    (exists t : M, Satisfies gamma (UpdateV rho x t) phi)
    <->
    Satisfies gamma rho (Exists x phi).

  Axiom SatAnd : forall rho phi phi' gamma,
    (Satisfies gamma rho phi /\ Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (And phi phi').

  Axiom SatOr : forall rho phi phi' gamma,
    (Satisfies gamma rho phi \/ Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (Or phi phi').

  Axiom SatImplies : forall rho phi phi' gamma,
    (Satisfies gamma rho phi -> Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (Implies phi phi').

  Axiom SatPattern : forall rho t gamma,
    (Some gamma = value rho t)
    <->
    Satisfies gamma rho (Pattern t).

End Satisfaction.

Module Type ObjectLanguage.
  Declare Module Export Base : Terms.
  Declare Module Export BaseM : Model Base.
  Declare Module Export BaseF : Formulas Base.
  Declare Module Export BaseS : Satisfaction Base BaseM BaseF.
End ObjectLanguage.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Setoid.

Section FixDomain.

Print Acc.

Print relation.

Variable M : Set.

  Definition terminates (gamma : M) (R : relation M) :=
    Acc R gamma.

(*

R x y    =    x \prec y

inductively:

- prove that all predecesors of gamma are R-accesible
- then gamma is R-accesible

*)

  Inductive clos (A : Type) (R : A -> A -> Prop) : bool -> A -> A -> Prop :=
  | clos_refl : forall a, clos A R false a a
  | clos_step : forall s a b, R a b -> clos A R s a b
  | clos_trans : forall s a b c,
    clos A R s a b -> clos A R s b c -> clos A R s a c. 

  Lemma clos_faithful (A : Type) (R : relation A) (strict : bool) :
    forall l r,
      clos A R strict l r <->
      if strict
        then Relation_Operators.clos_trans A R l r
        else clos_refl_trans A R l r.
  Proof.
    split.
      induction 1; try (destruct s); econstructor solve[eauto].
      destruct strict; induction 1; econstructor solve[eauto].
  Qed.

  Definition clos_unstrict A (R : relation A) a b
    (step : clos A R true a b) : clos A R false a b.
  Proof.
    induction step; eauto using clos.
  Defined.

  Inductive clos_left (A : Type) (R : A -> A -> Prop) :
    bool -> A -> A -> Prop :=
  | clos_left_refl : forall a, clos_left A R false a a
  | clos_left_step : forall s a b, R a b -> clos_left A R s a b
  | clos_left_ext : forall s a b c,
    R a b -> clos_left A R s b c -> clos_left A R s a c.
  
  Lemma clos_left_trans (A : Type) (R : A -> A -> Prop)
    strict a b c :
    clos_left A R strict a b -> clos_left A R strict b c ->
    clos_left A R strict a c.
    induction 1.  
    auto.
    apply clos_left_ext. assumption.
    intros. specialize (IHclos_left H1).
    eapply clos_left_ext; eassumption.
  Qed.

  Lemma clos_iff_left (A : Type) (R : A -> A -> Prop)
    strict a b : clos A R strict a b <-> clos_left A R strict a b.
  Proof.  
    split.
    induction 1.
    constructor.
    constructor;assumption.
    eapply clos_left_trans;eassumption.
    
    induction 1.
    constructor.
    constructor;assumption.
    eauto using clos.
  Qed.

  Lemma clos_cons_lt A (R : relation A) a b s c :
    clos A R true a b -> clos A R s b c -> clos A R true a c.
  Proof. induction 2;eauto using clos. Qed.

  Lemma clos_trans_lt A (R : relation A) a b s c :
    clos A R s a b -> clos A R false b c -> clos A R s a c.
  Proof. destruct s; eauto using clos_cons_lt, clos. Qed.

  Lemma clos_cons_rt A (R : relation A) a s b c :
    clos A R s a b -> clos A R true b c -> clos A R true a c.
  Proof. induction 1;eauto using clos. Qed.

  Lemma clos_cat A (R : relation A) a s1 b s2 c :
    clos A R s1 a b -> clos A R s2 b c -> clos A R (orb s1 s2) a c.
  Proof.
    destruct s1. apply clos_cons_lt.
    destruct s2. apply clos_cons_rt.
    apply clos_trans.
  Qed.

  Lemma clos_cat' A (R : relation A) a s1 b s2 s3 c :
    clos A R s1 a b -> clos A R s2 b c -> s3 = orb s1 s2 -> clos A R s3 a c.
  Proof.
    destruct s1; destruct s2; intros; rewrite H1; eapply clos_cat; eauto.
  Qed.

  Definition impliesb (a b : bool) :=
    a = false \/ b = true.

  Lemma clos_cat'' A (R : relation A) a s1 b s2 s3 c :
    clos A R s1 a b -> clos A R s2 b c -> impliesb s3 (orb s1 s2) -> clos A R s3 a c.
  Proof.
    intros; destruct s1; destruct s2; destruct s3.
    eapply clos_cat'; eauto.
    try (apply clos_unstrict; eauto using clos ).
    eapply (clos_cat' A R _ _ _ _ _ _ H H0). compute. reflexivity.
    try (apply clos_unstrict; eauto using clos ).
    eapply (clos_cat' A R _ _ _ _ _ _ H H0). compute. reflexivity.
    eapply (clos_cat' A R _ _ _ _ _ _ H H0). compute. reflexivity.
    try (apply clos_unstrict; eauto using clos ).
    eapply (clos_cat' A R _ _ _ _ _ _ H H0). compute. reflexivity.
    compute in H1; destruct H1; inversion H1. 
    eapply (clos_cat' A R _ _ _ _ _ _ H H0). compute. reflexivity.
Qed.    

  Lemma terminates_fwd (R : relation M) (gamma : M) :
    terminates gamma R ->
    forall strict gamma', clos M R strict gamma' gamma ->
      terminates gamma' R.
  Proof.
    intros.
    induction H0.
    assumption.
    destruct H. apply H. assumption.
    auto.
  Qed.

(*  Lemma terminates_trans (R : relation M) (gamma : M) :
    terminates gamma R -> terminates gamma (clos M R true).
  Proof.
    induction 1.
    constructor.
    intros.
    rewrite clos_iff_left in H1.
    remember true as strict; destruct H1.
    discriminate.
    subst s.
    apply H0. assumption.
    apply terminates_fwd with b true.
    apply H0. assumption.
    rewrite <- clos_iff_left in H2.
    subst.
    constructor. assumption.
  Qed.
*)
  Lemma clos_weaken (A : Type) (R1 R2 : relation A) strict x y :
    (forall a b, R1 a b -> R2 a b) ->
    clos A R1 strict x y -> clos A R2 strict x y.
  Proof. induction 2; eauto using clos. Defined.

(* Could be loosened to only require the weakening
   for values under x *)
  Lemma Acc_weaken A (R1 R2 : relation A)
    (HWeak : forall a b, R2 a b -> R1 a b)
    (x : A) : Acc R1 x -> Acc R2 x.
  Proof. induction 1; constructor; auto. Qed.

End FixDomain.

Module MatchLReduction(Base : ObjectLanguage).

  Export Base.

  Definition SimpleRule := (Formula * Formula) % type.

  Definition SimpleSystem := SimpleRule -> Prop.

  Definition CondRule := (SimpleRule * SimpleSystem) % type.

  Definition CondSystem := CondRule -> Prop.

  Variable S : CondSystem.

  Definition rho_valid_srule (rule : SimpleRule) (rho : Valuation) (ts : relation M) :=
    forall gamma',
      Satisfies gamma' rho (fst rule) ->
      exists gamma'',
        (clos M ts false) gamma' gamma'' /\ Satisfies gamma'' rho (snd rule).

  Definition rho_valid_ssys (ssys : SimpleSystem) (rho : Valuation) (ts : relation M) :=
    forall rule,
      ssys rule -> rho_valid_srule rule rho ts.

  Inductive ts (csys : CondSystem) : (relation M) :=
    | ts_rule :
      forall (rule : CondRule),
        csys rule ->
        forall (rho : Valuation),
          forall gamma' gamma'',
            Satisfies gamma' rho (fst (fst rule)) ->
            Satisfies gamma'' rho (snd (fst rule)) ->
            rho_valid_ssys (snd rule) rho (ts csys) ->
              ts csys gamma' gamma''.
 
(*
gamma-soundness

phi' => phi'' is gamma_0-sound if

forall gamma' < gamma,
  gamma' rho satisfies phi'
  there exists
    gamma'' such that
    gamma'' rho satisfies phi''
*)

  (* gamma' < gamma'' -- replace gamma' <-> gamma'' *)
  Definition less_than (csys : CondSystem) gamma' gamma'' :=
    ts csys gamma'' gamma' \/  
    exists rule : CondRule,   
      exists rho : Valuation,
        Satisfies gamma'' rho (fst (fst rule)) /\
        exists rule_side : SimpleRule,          
          (csys rule /\
            (snd rule) rule_side /\
            Satisfies gamma' rho (fst rule_side)). 

  (* remove closure, leave less_than *)
  Definition opterminates (csys : CondSystem) gamma :=
    terminates M gamma (clos M (less_than csys) true).

End MatchLReduction.

Module MatchLProofSystem (Base : ObjectLanguage).

  Export Base.

  Module Reduction := MatchLReduction Base.
  Export Reduction.

  Definition is_empty (ssys : SimpleSystem) :=
    forall rule,
      ssys rule -> False.
  
  Require Import Logic.Decidable.

  (* Hypothesis is_empty_dec : *)
  (*   forall ssys : SimpleSystem, Decidable.decidable (is_empty ssys). *)

  Definition empty_ssys : SimpleSystem :=
    fun r => False.

  Definition IsEmpty : SimpleSystem -> Prop :=
    fun sys => forall rule, ~ sys rule.

  Definition crule_from_srule (srule : SimpleRule) : CondRule :=
    (srule, empty_ssys).

  Definition csys_from_ssys (ssys : SimpleSystem) : CondSystem :=
    fun crule =>
      exists srule,
        (ssys srule /\
          crule = crule_from_srule srule).

  Definition union_csys (csys1 : CondSystem) (csys2 : CondSystem) : CondSystem :=
    fun crule =>
      csys1 crule \/
      csys2 crule.

  Definition cons_ssys phi phi' (ssys : SimpleSystem) : SimpleSystem :=
    fun srule =>
      srule = (phi, phi') \/
      ssys srule.

  Locate "\/".
  Print or.

  Definition union_ssys (ssys1 ssys2 : SimpleSystem) : SimpleSystem :=
    fun srule => (ssys1 srule \/  ssys2 srule).

  Inductive PS : SimpleSystem -> SimpleSystem -> Formula -> Formula -> Prop :=
  | ps_axiom_S : 
    forall A C psi crule,
      S crule ->
      stateless psi ->
      (forall srule,
        (snd crule) srule ->
        PS (union_ssys A C) empty_ssys (And (fst srule) psi) (snd srule)) ->
      PS A C (And (fst (fst crule)) psi) (And (snd (fst crule)) psi)
  | ps_axiom_A :
    forall (A : SimpleSystem) (C : SimpleSystem) psi srule,
      A srule ->
      stateless psi ->
      PS A C (And (fst srule) psi) (And (snd srule) psi)
  | ps_refl :
    forall A C phi,
      IsEmpty C ->
      PS A C phi phi
  | ps_trans :
    forall A C phi1 phi2 phi3,
      PS A C phi1 phi2 ->
      PS (union_ssys A C) empty_ssys phi2 phi3 ->
      PS A C phi1 phi3
  | ps_conseq :
    forall A C phi1 phi1' phi2 phi2',
      Valid (Implies phi1 phi1') ->
      PS A C phi1' phi2' ->
      Valid (Implies phi2' phi2) ->
      PS A C phi1 phi2
  | ps_case :
    forall A C phi1 phi phi2,
      PS A C phi1 phi ->
      PS A C phi2 phi ->
      PS A C (Or phi1 phi2) phi
  | ps_abstr :
    forall A C X phi phi',
      PS A C phi phi' ->
      notFree X phi' ->
      PS A C (Exists X phi) phi'
  | ps_circ :
    forall A C phi phi',
      PS A (cons_ssys phi phi' C) phi phi' ->
      PS A C phi phi'.

End MatchLProofSystem.

Module MatchLSoundness (Base : ObjectLanguage).
  
  Export Base.

  Module ProofSystem := MatchLProofSystem Base.
  Export ProofSystem.


(* S \models phi' => phi'' = soundness *)
    
    Definition sound_srule (strict : bool) (srule : SimpleRule) : Prop :=
      forall gamma',
        opterminates S gamma' ->
        forall rho,
          Satisfies gamma' rho (fst srule) ->
          exists gamma'',
            clos M (ts S) strict gamma' gamma'' /\
            Satisfies gamma'' rho (snd srule).
         
    Definition gamma_sound_srule (strict : bool) (srule : SimpleRule) gamma : Prop :=
      forall gamma',
        clos M (less_than S) false gamma' gamma ->
        forall rho,
          Satisfies gamma' rho (fst srule) ->
          exists gamma'',
            clos M (ts S) strict gamma' gamma'' /\
            Satisfies gamma'' rho (snd srule).

    Definition gamma_sound_ssys (strict : bool) (ssys : SimpleSystem) gamma : Prop :=
      forall srule,
        ssys srule ->
        gamma_sound_srule strict srule gamma.

    Lemma gamma_sound_unstrict :
      forall gamma srule,
        gamma_sound_srule true srule gamma ->
        gamma_sound_srule false srule gamma.
      unfold gamma_sound_srule.
      intros.
      specialize (H gamma' H0 rho H1).
      elim H; intro gamma''. intros.
      exists gamma''. split.
      apply clos_unstrict. apply H2. apply H2.
    Qed.

    Lemma ts_to_lt :
      forall gamma' gamma'' s,
        clos M (ts S) s gamma' gamma'' ->
        clos M (less_than S) s gamma'' gamma'.
      intros.
      induction H.
      apply clos_refl.
      apply clos_step.
      unfold less_than.
      left.
      assumption.
      eapply clos_trans.
      apply IHclos2.
      apply IHclos1.
    Qed.

    Lemma gamma_sound_trans : forall phi1 phi2 phi3 gamma s1 s2 s3,
      gamma_sound_srule s1 (phi1, phi2) gamma ->
      gamma_sound_srule s2 (phi2, phi3) gamma ->
      s3 = orb s1 s2 ->
      gamma_sound_srule s3 (phi1, phi3) gamma.
      unfold gamma_sound_srule; intros; remember s2 as rem; destruct s1; destruct s2; destruct s3; simpl; rewrite Heqrem in *.

      specialize (H gamma' H2 rho H3);
        elim H; intros;
          specialize (H0 x);
            assert (Hbelea : clos M (less_than S) false x gamma).
      eapply clos_cat'' ; [
       apply ts_to_lt ; apply H4 |
       apply H2 |
       simpl ; compute ; tauto ].
      simpl in *;
      decompose [and] H4.
        simpl.
        specialize (H0 Hbelea rho H6);
      elim H0; intros;
      exists x0.
      split ; [
        eapply clos_cat' ; [ apply H5 | apply H7 | simpl in *; reflexivity ] |
          apply H7 ].

      inversion H1.

      specialize (H gamma' H2 rho H3);
        elim H; intros;
          specialize (H0 x);
            assert (Hbelea : clos M (less_than S) false x gamma).
      eapply clos_cat'' ; [
       apply ts_to_lt ; apply H4 |
       apply H2 |
       simpl ; compute ; tauto ].
      simpl in *;
      decompose [and] H4.
        simpl.
        specialize (H0 Hbelea rho H6);
      elim H0; intros;
      exists x0.
      split ; [
        eapply clos_cat' ; [ apply H5 | apply H7 | simpl in *; reflexivity ] |
          apply H7 ].

      inversion H1.

      specialize (H gamma' H2 rho H3);
        elim H; intros;
          specialize (H0 x);
            assert (Hbelea : clos M (less_than S) false x gamma).
      eapply clos_cat'' ; [
       apply ts_to_lt ; apply H4 |
       apply H2 |
       simpl ; compute ; tauto ].
      simpl in *;
      decompose [and] H4.
        simpl.
        specialize (H0 Hbelea rho H6);
      elim H0; intros;
      exists x0.
      split ; [
        eapply clos_cat' ; [ apply H5 | apply H7 | simpl in *; reflexivity ] |
          apply H7 ].

      inversion H1.
      inversion H1.

      specialize (H gamma' H2 rho H3);
        elim H; intros;
          specialize (H0 x);
            assert (Hbelea : clos M (less_than S) false x gamma).
      eapply clos_cat'' ; [
       apply ts_to_lt ; apply H4 |
       apply H2 |
       simpl ; compute ; tauto ].
      simpl in *;
      decompose [and] H4.
        simpl.
        specialize (H0 Hbelea rho H6);
      elim H0; intros;
      exists x0.
      split ; [
        eapply clos_cat' ; [ apply H5 | apply H7 | simpl in *; reflexivity ] |
          apply H7 ].
    Qed.

    Lemma sound_union :
      forall gamma A B s1 s2 s3,
        gamma_sound_ssys s1 A gamma ->
        gamma_sound_ssys s2 B gamma ->
        s3 = andb s1 s2 ->
        gamma_sound_ssys s3 (union_ssys A B) gamma.
      unfold gamma_sound_ssys.
      unfold  union_ssys.
      intros.
      destruct H2; destruct s1; destruct s2; simpl in H1; rewrite H1; 
        auto; try apply gamma_sound_unstrict; auto.
    Qed.

      

    (* Lemma sound_iff_gamma_sound : *)
    (*   forall phi' phi'' strict, *)
    (*     sound_srule strict (phi', phi'') <-> *)
    (*     (forall gamma, *)
    (*       gamma_sound_srule strict (phi', phi'') gamma). *)
    (*   admit. *)
    (* Qed. *)

    Definition well_defined crule : Prop :=
      forall gamma' rho,
        Satisfies gamma' rho (fst (fst crule)) ->
        rho_valid_ssys (snd crule) rho (ts S) ->
        exists gamma'',
          clos M (ts S) true gamma' gamma'' /\
          Satisfies gamma'' rho (snd (fst crule)).

    Hypothesis well_defined_S : forall crule,
      S crule -> well_defined crule.

    Definition is_simple_rule (crule : CondRule) :=
      is_empty (snd crule).

    Definition cond_rules_wd (A : CondSystem) :=
      forall crule,
        A crule ->
        (not (is_simple_rule crule)) ->
        well_defined crule.

    Definition simple_rules_gamma_sound (A : CondSystem) gamma :=
      forall crule,
        A crule ->
        is_empty (snd crule) ->
        gamma_sound_srule true (fst crule) gamma.

    Definition gamma_almost_ssys (strict : bool) (C : SimpleSystem) gamma :=
      forall gamma_0,
        clos M (less_than S) true gamma_0 gamma ->
        gamma_sound_ssys strict C gamma_0.

Definition inCS_ (x : CondRule) (y : CondSystem) := y x.

Notation "x 'inCS' y" := (inCS_ x y) (at level 60).

    Lemma belea : forall (crule : CondRule) A gamma,
      crule inCS A ->
      is_simple_rule crule ->
      simple_rules_gamma_sound A gamma ->
      forall srule side_conditions,
        crule = (srule, side_conditions) -> 
        gamma_sound_srule true srule gamma.
      intros.
      replace srule with (fst crule).
      auto.
      rewrite H2.
      auto.
    Qed.

    Lemma belea' : forall (crule : CondRule),
      crule inCS S ->
      forall srule side_conditions,
        crule = (srule, side_conditions) ->
        forall (rule : SimpleRule),
          side_conditions rule ->
          forall gamma',
            opterminates S gamma' ->
            forall rho gamma_i',
              Satisfies gamma' rho (fst srule) ->
              Satisfies gamma_i' rho (fst rule) ->
              less_than S gamma_i' gamma'.
      Proof.
        intros.
        unfold less_than.
        right.
        exists crule. exists rho. 

        split. rewrite H0. assumption.
        exists rule. split. assumption.
        split. rewrite H0. assumption.
        assumption.
      Qed.

Notation "gamma 'optermin' system" := (opterminates system gamma) (at level 60).

Lemma belea'' : forall gamma gamma',
  gamma optermin S ->
  less_than S gamma' gamma ->
  gamma' optermin S.
Proof.
  unfold opterminates.
  unfold terminates.
  intros.
  inversion H.
  apply H1.
  apply clos_step.
  assumption.
Qed.

Lemma belea''' : forall strict gamma gamma',
  gamma optermin S ->
  clos M (less_than S) strict gamma' gamma ->
  gamma' optermin S.
Proof.
  unfold opterminates.
  induction 2.
  assumption.
  eapply belea''. apply H. apply H0.
  apply IHclos1. apply IHclos2. assumption.
Qed.

Lemma sound_weaken : forall strict gamma gamma0 phi phi',
  gamma_sound_srule strict (phi, phi') gamma ->
  less_than S gamma0 gamma ->
  gamma_sound_srule strict (phi, phi') gamma0.
  Proof.
    intros.
    unfold gamma_sound_srule.
    intros.
    assert (Hless : clos M (less_than S) false gamma' gamma).
    eapply clos_trans.
    apply H1.
    apply clos_step.
    assumption.
    unfold gamma_sound_srule in H.
    specialize (H gamma' Hless rho H2).
    assumption.
Qed.    

Lemma sound_weaken' : forall strict gamma gamma0 phi phi',
  gamma_sound_srule strict (phi, phi') gamma ->
  clos M (less_than S) false gamma0 gamma ->
  gamma_sound_srule strict (phi, phi') gamma0.
  Proof.
    induction 2.
    assumption.
    eapply sound_weaken. apply H. apply H0.
    apply IHclos1. apply IHclos2. assumption.
Qed.

Lemma trans_help : forall M (R : relation M) a b c,
  clos M R false b c ->
  clos M R true a b ->
  clos M R true a c.
Proof.
  intros.
  eapply clos_cons_lt.
  apply H0.
  apply H.
Qed.

  (* Lemma clos_cons_lt A (R : relation A) a b s c : *)
  (*   clos A R true a b -> clos A R s b c -> clos A R true a c. *)
  (* Proof. induction 2;eauto using clos. Qed. *)

  (* Lemma clos_trans_lt A (R : relation A) a b s c : *)
  (*   clos A R s a b -> clos A R false b c -> clos A R s a c. *)
  (* Proof. destruct s; eauto using clos_cons_lt, clos. Qed. *)

  (* Lemma clos_cons_rt A (R : relation A) a s b c : *)
  (*   clos A R s a b -> clos A R true b c -> clos A R true a c. *)
  (* Proof. induction 1;eauto using clos. Qed. *)

Lemma sound_unstrict :
  forall phi phi' gamma,
    gamma_sound_srule true (phi, phi') gamma ->
    gamma_sound_srule false (phi, phi') gamma.
  intros.
  unfold gamma_sound_srule in *.
  intros.
  specialize (H gamma' H0 rho H1).
  elim H; intros.
  exists x.
  split.
  apply clos_unstrict.
  apply H2.
  apply H2.
Qed.


    Theorem soundness :
      forall A C phi' phi'',
        PS A C phi' phi'' ->
        forall gamma,
          gamma optermin S ->
          gamma_sound_ssys true A gamma ->
          gamma_almost_ssys true C gamma ->
          ((is_empty C -> gamma_sound_srule false (phi', phi'') gamma) /\
            ((not (is_empty C))  -> gamma_sound_srule true (phi', phi'') gamma)).
    Proof.
      induction 1.

      Case "Axiom S".

      destruct crule as [ srule side ].
      simpl.

      intros gamma HT HA HC.

      split; intro Hempty.

      SCase "empty circularities".

      unfold gamma_sound_srule.
      intros gamma' Hless rho Hgamma'.
     
      assert (Hside : forall rule, side rule -> rho_valid_srule rule rho (ts S)).
      intros rule Hrule_side.
      unfold rho_valid_srule.
      intros gamma_i' Hgamma_i'.
      
      assert (Hless' : less_than S gamma_i' gamma'). eapply belea'. apply H. apply eq_refl. apply Hrule_side.
      eapply belea'''. apply HT. apply Hless.
      simpl in Hgamma'.
      rewrite <- SatAnd in Hgamma'.
      apply Hgamma'.
      assumption.
      
      assert (Hsound_i' : gamma_sound_ssys true (union_ssys A C) gamma_i').
      
      unfold gamma_sound_ssys.
      intro ruleAC.
      destruct 1.

      unfold gamma_sound_ssys in HA.
      eapply sound_weaken'.
      apply HA.
      destruct ruleAC; simpl; assumption.
      eapply clos_trans. apply clos_step. apply Hless'. assumption.

      unfold gamma_sound_ssys in HA.
      eapply sound_weaken'.
      apply HC.
      eapply trans_help. apply Hless. apply clos_step. apply Hless'.
      
      destruct ruleAC; simpl; assumption.
      apply clos_refl.

      specialize (H2 rule Hrule_side gamma_i').

      assert (Hterm_i' : gamma_i' optermin S).
      eapply belea'''. apply HT. eapply clos_trans. apply clos_step. apply Hless'. apply Hless.
      specialize (H2 Hterm_i' Hsound_i').
      
      assert (Hcool : gamma_almost_ssys true empty_ssys gamma_i').
      unfold gamma_almost_ssys.
      unfold empty_ssys.
      intros.
      unfold gamma_sound_ssys.
      intros.
      exfalso; apply H4.

      specialize (H2 Hcool).
      decompose [and] H2.
      assert (is_empty empty_ssys).
      unfold is_empty. unfold empty_ssys. trivial.
      specialize (H3 H5).
      unfold gamma_sound_srule in H3.
      specialize (H3 gamma_i').
      specialize (H3 (clos_refl _ _ _)).
      specialize (H3 rho).

      assert (Satisfies gamma_i' rho (fst (And (fst rule) psi, snd rule))).
      apply SatAnd.
      split.
      assumption.
      eapply stateless_sat.
      assumption. simpl in Hgamma'.
      rewrite <- SatAnd in Hgamma'.
      apply Hgamma'.
      
      specialize (H3 H6).
      elim H3; intros.
      exists x.
      split.
      simpl in H7.
      apply H7. apply H7.
      simpl in Hgamma'.
      rewrite <- SatAnd in Hgamma'.
      decompose [and] Hgamma'.

      assert (H_wd : well_defined (srule, side)) by (apply (well_defined_S _ H)).
      unfold well_defined in H_wd.
      specialize (H_wd gamma' rho H3 Hside).
      
      elim H_wd; intros.
      exists x.
      split. apply clos_unstrict. apply H5.
      simpl. rewrite <- SatAnd.
      split. apply H5.
      eapply stateless_sat. assumption. apply H4.

      SCase "non-empty circularities".

      unfold gamma_sound_srule.
      intros gamma' Hless rho Hgamma'.
     
      assert (Hside : forall rule, side rule -> rho_valid_srule rule rho (ts S)).
      intros rule Hrule_side.
      unfold rho_valid_srule.
      intros gamma_i' Hgamma_i'.
      
      assert (Hless' : less_than S gamma_i' gamma'). eapply belea'. apply H. apply eq_refl. apply Hrule_side.
      eapply belea'''. apply HT. apply Hless.
      simpl in Hgamma'.
      rewrite <- SatAnd in Hgamma'.
      apply Hgamma'.
      assumption.
      
      assert (Hsound_i' : gamma_sound_ssys true (union_ssys A C) gamma_i').
      
      unfold gamma_sound_ssys.
      intro ruleAC.
      destruct 1.

      unfold gamma_sound_ssys in HA.
      eapply sound_weaken'.
      apply HA.
      destruct ruleAC; simpl; assumption.
      eapply clos_trans. apply clos_step. apply Hless'. assumption.

      unfold gamma_sound_ssys in HA.
      eapply sound_weaken'.
      apply HC.
      eapply trans_help. apply Hless. apply clos_step. apply Hless'.
      
      destruct ruleAC; simpl; assumption.
      apply clos_refl.

      specialize (H2 rule Hrule_side gamma_i').

      assert (Hterm_i' : gamma_i' optermin S).
      eapply belea'''. apply HT. eapply clos_trans. apply clos_step. apply Hless'. apply Hless.
      specialize (H2 Hterm_i' Hsound_i').
      
      assert (Hcool : gamma_almost_ssys true empty_ssys gamma_i').
      unfold gamma_almost_ssys.
      unfold empty_ssys.
      intros.
      unfold gamma_sound_ssys.
      intros.
      exfalso; apply H4.

      specialize (H2 Hcool).
      decompose [and] H2.
      assert (is_empty empty_ssys).
      unfold is_empty. unfold empty_ssys. trivial.
      specialize (H3 H5).
      unfold gamma_sound_srule in H3.
      specialize (H3 gamma_i').
      specialize (H3 (clos_refl _ _ _)).
      specialize (H3 rho).

      assert (Satisfies gamma_i' rho (fst (And (fst rule) psi, snd rule))).
      apply SatAnd.
      split.
      assumption.
      eapply stateless_sat.
      assumption. simpl in Hgamma'.
      rewrite <- SatAnd in Hgamma'.
      apply Hgamma'.
      
      specialize (H3 H6).
      elim H3; intros.
      exists x.
      split.
      simpl in H7.
      apply H7. apply H7.
      simpl in Hgamma'.
      rewrite <- SatAnd in Hgamma'.
      decompose [and] Hgamma'.

      assert (H_wd : well_defined (srule, side)) by (apply (well_defined_S _ H)).
      unfold well_defined in H_wd.
      specialize (H_wd gamma' rho H3 Hside).
      
      elim H_wd; intros.
      exists x.
      split. apply H5.
      simpl. rewrite <- SatAnd.
      split. apply H5.
      eapply stateless_sat. assumption. apply H4.

      Case "Axiom A".
      
      intros; split; intro HemptyC ;
        (unfold gamma_sound_srule; simpl; intros gamma' Hless rho Hsat';
          assert (Hsrule : gamma_sound_srule true srule gamma) by (apply H2; assumption);
            rewrite <- SatAnd in Hsat'; decompose [and] Hsat';
              unfold gamma_sound_srule in Hsrule;
                specialize (Hsrule gamma' Hless rho H4);
                  elim Hsrule; intros gamma''; intros; decompose [and] H6;
                    exists gamma''; split; [ try apply clos_unstrict; assumption |
                      apply SatAnd; split ; [ apply H8 | eapply stateless_sat ; [ apply H0 | apply H5 ]]]).

      Case "Reflexivity".
      intros. split; intros HemptyC.

      SCase "C is empty".
      unfold gamma_sound_srule; simpl; intros; exists gamma'; split ; [ apply clos_refl | assumption ].
      
      SCase "C is not empty".
      unfold is_empty in HemptyC. unfold empty_ssys in HemptyC. tauto.

      Case "Transitivity".
      intros gamma HT HA HC; split; intros HemptyC.

      SCase "C is empty".

      specialize (IHPS1 gamma HT HA HC).
      specialize (IHPS2 gamma HT).

      assert (HA' : gamma_sound_ssys true (union_ssys A C) gamma).
      eapply sound_union. apply HA.
      unfold gamma_sound_ssys; unfold is_empty in HemptyC; intros; exfalso; eapply HemptyC. apply H1.
      reflexivity.
      
      assert (HC' : gamma_almost_ssys true empty_ssys gamma).
      unfold gamma_almost_ssys; unfold empty_ssys; firstorder.

      specialize (IHPS2 HA' HC').
      decompose [and] IHPS1. decompose [and] IHPS2.
      eapply gamma_sound_trans. apply H1. assumption. apply H3.
      unfold is_empty. unfold empty_ssys. tauto.
      compute. reflexivity.

      SCase "C is not empty".
      specialize (IHPS1 gamma HT HA HC).
      unfold gamma_sound_srule.
      intros gamma1 Htransition rho Hsat.
      decompose [and] IHPS1.
      clear H1.
      clear IHPS1.
      rename H2 into Hind1.
      specialize (Hind1 HemptyC).
      unfold gamma_sound_srule in Hind1.
      specialize (Hind1 gamma1 Htransition rho Hsat).
      elim Hind1; intros gamma2; intros.
      decompose [and] H1.
      clear H1.
      rename H2 into Htrans2.
      rename H3 into Hsat2.
      specialize (IHPS2 gamma2).

      assert (Hlt2 : clos M (less_than S) true gamma2 gamma).
      eapply clos_cat'.
      apply ts_to_lt.
      apply Htrans2.
      apply Htransition.
      compute. reflexivity.

      assert (HT2 : gamma2 optermin S).
      eapply belea'''.
      apply HT.
      apply Hlt2.
      specialize (IHPS2 HT2).
      
      assert (Hsound2 : gamma_sound_ssys true (union_ssys A C) gamma2).
      eapply sound_union.
      SSCase "sound w.r.t. A".
      unfold gamma_sound_ssys.
      intros.
      eapply sound_weaken'.
      apply HA.
      destruct srule; simpl; apply H1.
      apply clos_unstrict.
      assumption.

      SSCase "sound w.r.t. C".
      unfold gamma_almost_ssys in HC.
      apply HC.
      assumption.
      reflexivity.
      specialize (IHPS2 Hsound2).
      
      
      assert (Hemptysound : gamma_almost_ssys true empty_ssys gamma2).
      unfold gamma_almost_ssys.
      unfold empty_ssys.
      intros.
      unfold gamma_sound_ssys.
      intros.
      exfalso. assumption.
      specialize (IHPS2 Hemptysound).
      decompose [and] IHPS2.
      clear H2.
      clear IHPS2.
      rename H1 into Hind2.

      assert (Hemptyempty : is_empty empty_ssys).
      compute; intros; exfalso; assumption.
      specialize (Hind2 Hemptyempty).

      unfold gamma_sound_srule in Hind2.
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
      apply H1.
      compute. right. reflexivity.
      assumption.

      Case "Consequence".
      rename H into V1.
      rename H1 into V2.
      intros gamma HT HA HC.
      specialize (IHPS gamma HT HA HC).
      decompose [and] IHPS.
      rename H into HeC.
      rename H1 into HneC.
      split; intro Hemptyness.
      
      SCase "C is empty".
      specialize (HeC Hemptyness).
      unfold gamma_sound_srule.
      intros gamma' Htrans rho Hsat.
      unfold Valid in V1.
      specialize (V1 gamma' rho).
      rewrite <- SatImplies in V1.
      specialize (V1 Hsat).
      unfold gamma_sound_srule in HeC.
      specialize (HeC gamma' Htrans rho V1).
      elim HeC; intros gamma'' Hand.
      decompose [and] Hand; clear Hand; rename H into Htrans';
        rename H1 into Hsat'.
      unfold Valid in V2.
      specialize (V2 gamma'' rho).
      rewrite <- SatImplies in V2.
      specialize (V2 Hsat').
      exists gamma''.
      split; assumption.

      SCase "C not empty".
      specialize (HneC Hemptyness).
      unfold gamma_sound_srule.
      intros gamma' Htrans rho Hsat.
      unfold Valid in V1.
      specialize (V1 gamma' rho).
      rewrite <- SatImplies in V1.
      specialize (V1 Hsat).
      unfold gamma_sound_srule in HeC.
      specialize (HneC gamma' Htrans rho V1).
      elim HneC; intros gamma'' Hand.
      decompose [and] Hand; clear Hand; rename H into Htrans';
        rename H1 into Hsat'.
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
      rename H1 into He1.
      rename H2 into Hne1.
      rename H3 into He2.
      rename H4 into Hne2.
      split.
      SCase "empty C".
      intros Hempty.
      specialize (He1 Hempty).
      specialize (He2 Hempty).
      unfold gamma_sound_srule.
      intros gamma' Htrans rho Hsat.
      simpl in Hsat.
      rewrite <- SatOr in Hsat.
      destruct Hsat.
      unfold gamma_sound_srule in He1.
      specialize (He1 gamma' Htrans rho H1).
      elim He1; intros gamma'' Hand.
      decompose [and] Hand.
      exists gamma'' ; split; assumption.
      unfold gamma_sound_srule in He1.
      specialize (He2 gamma' Htrans rho H1).
      elim He2; intros gamma'' Hand.
      decompose [and] Hand.
      exists gamma'' ; split; assumption.
      
      SCase "not empty C".
      intros Hempty.
      specialize (Hne1 Hempty).
      specialize (Hne2 Hempty).
      unfold gamma_sound_srule.
      intros gamma' Htrans rho Hsat.
      simpl in Hsat.
      rewrite <- SatOr in Hsat.
      destruct Hsat.
      unfold gamma_sound_srule in He1.
      specialize (Hne1 gamma' Htrans rho H1).
      elim Hne1; intros gamma'' Hand.
      decompose [and] Hand.
      exists gamma'' ; split; assumption.
      unfold gamma_sound_srule in He1.
      specialize (Hne2 gamma' Htrans rho H1).
      elim Hne2; intros gamma'' Hand.
      decompose [and] Hand.
      exists gamma'' ; split; assumption.

      Case "abstraction".
      intros gamma HT HA HC; split; intros Hempty.
      SCase "empty C".
      unfold gamma_sound_srule.
      intros gamma' Htrans rho Hsat.
      simpl in Hsat.
      rewrite <- SatExists in Hsat.
      elim Hsat; intros gamma0 Hsat0.
      specialize (IHPS gamma HT HA HC).
      decompose [and] IHPS.
      specialize (H1 Hempty).
      unfold gamma_sound_srule in H1.
      specialize (H1 gamma' Htrans (UpdateV rho X gamma0) Hsat0).
      elim H1; intros gamma'' Hand.
      decompose [and] Hand.
      exists gamma''.
      split. assumption. simpl. simpl in H4.
      rewrite notFree_sat. apply H4. assumption.

      SCase "not empty C".
      unfold gamma_sound_srule.
      intros gamma' Htrans rho Hsat.
      simpl in Hsat.
      rewrite <- SatExists in Hsat.
      elim Hsat; intros gamma0 Hsat0.
      specialize (IHPS gamma HT HA HC).
      decompose [and] IHPS.
      specialize (H2 Hempty).
      unfold gamma_sound_srule in H1.
      specialize (H2 gamma' Htrans (UpdateV rho X gamma0) Hsat0).
      elim H2; intros gamma'' Hand.
      decompose [and] Hand.
      exists gamma''.
      split. assumption. simpl. simpl in H4.
      rewrite notFree_sat. apply H4. assumption.
      
      Case "Circularity".
      assert (forall gamma : M,
        gamma optermin S ->
        gamma_sound_ssys true A gamma ->
        gamma_almost_ssys true C gamma ->
        gamma_sound_srule true (phi, phi') gamma).
      induction 1.
      rename x into gamma.
      assert (gamma optermin S).
      unfold opterminates; unfold terminates.
      constructor; assumption.
      intros HA HC.

      specialize (IHPS gamma H2 HA).
      
      assert (Htoprove : gamma_almost_ssys true (cons_ssys phi phi' C) gamma).
      unfold gamma_almost_ssys.
      unfold cons_ssys.
      intros.
      unfold gamma_sound_ssys.
      intros.
      destruct H4.
      rewrite H4.
      apply H1.
      assumption.
      unfold gamma_sound_ssys; intros.
      eapply sound_weaken'.
      destruct srule0.
      apply HA.
      assumption.
      apply clos_unstrict.
      assumption.
      unfold gamma_almost_ssys.
      intros.
      unfold gamma_sound_ssys.
      intros.
      apply HC.
      eapply clos_cat''.
      apply H5. apply H3.
      compute. right. reflexivity.
      assumption.
      apply HC.
      assumption.
      assumption.
      
      specialize (IHPS Htoprove).
      decompose [and] IHPS.
      clear IHPS.
      clear H3.
      
      assert (Htoprove2 :  ~ is_empty (cons_ssys phi phi' C)).
      unfold is_empty.
      unfold cons_ssys.
      unfold not.
      intros.
      eapply H3.
      left. reflexivity.

      specialize (H4 Htoprove2).
      assumption.

      intros.
      split.
      intros.
      specialize (H0 gamma H1 H2 H3).
      apply sound_unstrict.
      intros.
      apply H0; assumption.
      intros.
      apply H0; assumption.
Qed.

Check soundness.

End MatchLSoundness.

(*

- engineer the proof
- ts = fix point instead of least fixed point
- prove the derived rules: substitution, framing

(* under axioms given up to alpha-renaming... *)
Framing:
"A |-_C phi => phi'" and stateless psi implies
"A |-_C phi /\ psi => phi' /\ psi"

Substitution:
"A |-_C phi => phi'" implies
"A |-_C sigma(phi) => sigma(phi')"

*)
