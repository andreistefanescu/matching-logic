Module FOL.

Parameter T : Set.

Parameter T_dec : forall x y : T, { x = y } + { x <> y }.

Parameter IsVariable : T -> Prop.

Definition Var : Set := { x : T & (IsVariable x) }.

Definition Substitution := Var -> T.

Parameter Apply : Substitution -> T -> T.

Parameter Update : Substitution -> Var -> T -> Substitution.

Inductive Formula : Set :=
  | Equals : T -> T -> Formula
  | And  : Formula -> Formula -> Formula
  | Not : Formula -> Formula
  | Forall : Var  -> Formula -> Formula.

Definition Valuation := Substitution.

Definition coerce (v : Var) := projS1 v.

Parameter Satisfies : Valuation -> Formula -> Prop.

Axiom SatEquals : forall rho : Valuation, forall t t' : T,
  Apply rho t = Apply rho t'
  <->
  Satisfies rho (Equals t t').

Axiom SatForall : forall rho : Valuation, forall x : Var, forall phi : Formula,
  (forall t : T, Satisfies (Update rho x t) phi)
  <->
  Satisfies rho (Forall x phi).

Axiom SatAnd : forall rho : Valuation, forall phi phi' : Formula,
  (Satisfies rho phi /\ Satisfies rho phi')
  <->
  Satisfies rho (And phi phi').

Axiom SatNot : forall rho : Valuation, forall phi : Formula,
  (~Satisfies rho phi)
  <->
  Satisfies rho (Not phi).

Fixpoint SatisfiesF (rho : Valuation) (phi : Formula) : Prop :=
  match phi with
    | Equals t1 t2 => (Apply rho t1 = Apply rho t2)
    | Forall v phi' => forall (s : T), SatisfiesF (Update rho v s) phi'
    | And phi1 phi2 => SatisfiesF rho phi1 /\ SatisfiesF rho phi2
    | Not phi' => ~SatisfiesF rho phi'
  end.

Require Import Setoid.

Theorem sameThing : forall (rho : Valuation) (phi : Formula),
  SatisfiesF rho phi <-> Satisfies rho phi.
  intros. generalize dependent rho.
  induction phi. intros. apply SatEquals.
  intros. simpl. rewrite IHphi1. rewrite IHphi2. apply SatAnd.
  intros. simpl. rewrite IHphi. apply SatNot.
  intros. simpl. split.
  rewrite <- SatForall. intros. apply IHphi. apply H.
  rewrite <- SatForall. intros. apply IHphi. apply H.
Qed.

Inductive SatI : Valuation -> Formula -> Prop :=
  | SatIEquals : forall rho : Valuation, forall t t' : T,
                  (Apply rho t = Apply rho t') ->
                    SatI rho (Equals t t')
  | SatIForall : forall rho : Valuation, forall x : Var, forall phi : Formula,
                  (forall t : T, SatI (Update rho x t) phi) ->
                        SatI rho (Forall x phi)
  | SatIAnd : forall rho : Valuation, forall phi phi' : Formula,
               SatI rho phi ->
                 SatI rho phi' ->
                   SatI rho (And phi phi')
  | SatINot : forall rho : Valuation, forall phi : Formula,
               (SatNI rho phi) ->
                 SatI rho (Not phi)
with SatNI : Valuation -> Formula -> Prop :=
  | SatNIEquals : forall rho : Valuation, forall t t' : T,
                  (Apply rho t <> Apply rho t') ->
                    SatNI rho (Equals t t')
  | SatNIForall : forall rho : Valuation, forall x : Var, forall phi : Formula, forall t : T,
    (SatI (Update rho x t) phi -> SatNI rho (Forall x phi))
  | SatNIAnd : forall rho : Valuation, forall phi phi' : Formula,
               (SatNI rho phi \/ SatNI rho phi') ->
                   SatNI rho (And phi phi')
  | SatNINot : forall rho : Valuation, forall phi : Formula,
               (SatI rho phi) ->
                 SatNI rho (Not phi).

(*Require Import Classical.

Theorem deMorgan : forall p q,
  ~ (p /\ q) <-> ~ p \/ ~ q.
  intros.
  apply NNPP. tauto.
Qed.

Theorem sameThing' : forall (rho : Valuation) (phi : Formula),
  (SatisfiesF rho phi <-> SatI rho phi) /\ ((~SatisfiesF rho phi) <-> SatNI rho phi).
  intros. generalize dependent rho.
  induction phi.
  intros.
     (* equals *)
    split.
      simpl. split. apply SatIEquals. intros. inversion H. assumption.
      simpl. split. intros. apply SatNIEquals. assumption. intros. inversion H. assumption.
      (* and *)
    split.
      simpl. split. intros. inversion H. constructor. apply IHphi1. assumption. apply IHphi2. assumption.
      simpl. split. inversion H. apply IHphi1. assumption. apply IHphi2. inversion H. assumption.
      simpl. setoid_replace (SatNI rho (And phi1 phi2)) with (~ SatisfiesF rho phi1 \/ ~ SatisfiesF rho phi2).
      apply deMorgan. setoid_replace (~ SatisfiesF rho phi1) with (SatNI rho phi1).
      setoid_replace (~ SatisfiesF rho phi2) with (SatNI rho phi2). split.
      inversion 1. assumption. intros. constructor. assumption.
      decompose [and] (IHphi1 rho). decompose [and] (IHphi2 rho).
      assumption. decompose [and] (IHphi1 rho). decompose [and] (IHphi2 rho).
      assumption.
      (* not *)
      intros. decompose [and] (IHphi rho).
      split. simpl. rewrite H0. split. intros. constructor. assumption.
      inversion 1. assumption.
      split. simpl. intros. constructor. apply H. apply NNPP. assumption.
      intros. inversion H1. simpl. tauto.
      (* forall *)
      intros.
      split. split.
      simpl. intros. constructor. intro. apply IHphi. apply H.
      simpl. intros. apply IHphi. inversion H. apply H2.
      split. unfold SatisfiesF. fold SatisfiesF. unfold not. intros.
      admit. admit.
Qed.
*)
Require Import Classical.

Theorem EM : forall (p : Prop), p \/ ~ p.
  intros.
  tauto.
Qed.

Theorem belea : forall D, forall P : D -> Prop,
  ~(forall x : D, P x) <-> (exists x : D, ~ P x).
  intros; split; intros.
  
  
Theorem sameThing'' : forall (t : T) (rho : Valuation) (phi : Formula),
  (Satisfies rho phi <-> SatI rho phi) /\ (~ Satisfies rho phi <-> SatNI rho phi).
  intros. generalize dependent rho.  generalize dependent t. induction phi.
  intros; split; split.
  (* equals *)
  simpl. rewrite <- SatEquals. intros. constructor. assumption.
  simpl. inversion 1. apply SatEquals. assumption.
  simpl. rewrite <- SatEquals. intros. econstructor. assumption.
  simpl. inversion 1. unfold not. rewrite <- SatEquals. intros. apply H2. assumption.
  (* and *)
  simpl; intros; split; split; decompose [and] (IHphi1 t rho); decompose [and] (IHphi2 t rho);
  intros. rewrite <- SatAnd in H3. decompose [and] H3. constructor. apply H. assumption. apply H1. assumption. apply SatAnd. split. inversion H3. apply H. assumption. apply H1. inversion H3. assumption.
  constructor. unfold not in H3. rewrite <- H0. rewrite <- H2. unfold not. rewrite <- SatAnd in H3.
  tauto. unfold not. intros. rewrite <- SatAnd in H4. inversion H3. rewrite <- H0 in H7. rewrite <- H2 in H7. tauto.
  (* not *)
  simpl; intros; split; split; decompose [and] (IHphi t rho); intros.
  rewrite <- SatNot in H1. constructor. tauto.
  inversion H1. apply SatNot. tauto.
  constructor. rewrite <- SatNot in H1. tauto.
  rewrite <- SatNot. inversion H1. tauto.
  (* forall *)
  intro.
  assert (forall rho : Valuation,
          (Satisfies rho phi <-> SatI rho phi)).
  apply IHphi.
  apply t.
  assert (forall rho : Valuation,
          (~Satisfies rho phi <-> SatNI rho phi)).
  apply IHphi.
  apply t.
  simpl; intros; split; split; intros.
  constructor. rewrite <- SatForall in H1. intros. apply H. apply H1.
  rewrite <- SatForall. inversion H1. intros. apply H. apply H4.
  rewrite <- SatForall in H1.
  apply SatNIForall with (t := t).
  setoid_rewrite <- H.
  