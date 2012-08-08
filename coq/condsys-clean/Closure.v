Require Import Relation_Definitions.
Require Import Relation_Operators.

Section FixDomain.

  Variable M : Set.

  Definition terminates (gamma : M) (R : relation M) :=
    Acc R gamma.

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

  Lemma clos_weaken (A : Type) (R1 R2 : relation A) strict x y :
    (forall a b, R1 a b -> R2 a b) ->
    clos A R1 strict x y -> clos A R2 strict x y.
  Proof. induction 2; eauto using clos. Defined.

  Lemma Acc_weaken A (R1 R2 : relation A)
    (HWeak : forall a b, R2 a b -> R1 a b)
    (x : A) : Acc R1 x -> Acc R2 x.
  Proof. induction 1; constructor; auto. Qed.

End FixDomain.
