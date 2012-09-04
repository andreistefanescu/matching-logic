Module FOL.

Parameter T : Set.

Parameter T_dec : forall x y : T, { x = y } + { x <> y }.

Parameter IsVariable : T -> Prop.

Definition Var : Set := { x : T & (IsVariable x) }.

Definition Substitution := Var -> T.

Hypothesis subst_dec : forall s s' : Substitution, { s = s' } + { s <> s' }.

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

Theorem sameThing : forall (phi : Formula) (rho : Valuation),
  SatisfiesF rho phi <-> Satisfies rho phi.
  induction phi.
  intros. apply SatEquals.
  intros. simpl. rewrite IHphi1. rewrite IHphi2. apply SatAnd.
  intros. simpl. rewrite IHphi. apply SatNot.
  intros. simpl. setoid_rewrite IHphi. apply SatForall.
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
  | SatNIForall : forall rho : Valuation, forall x : Var, forall phi : Formula,
    (exists t : T, SatNI (Update rho x t) phi) -> SatNI rho (Forall x phi)
  | SatNIAnd : forall rho : Valuation, forall phi phi' : Formula,
               (SatNI rho phi \/ SatNI rho phi') ->
                   SatNI rho (And phi phi')
  | SatNINot : forall rho : Valuation, forall phi : Formula,
               (SatI rho phi) ->
                 SatNI rho (Not phi).

Require Import Classical.

Theorem EM : forall (p : Prop), p \/ ~ p.
  intros.
  tauto.
Qed.

Theorem forall_exists : forall D, forall P : D -> Prop, ~ (forall d : D, P d) <->
  exists d : D, ~ P d.
split;[|firstorder]. (* only the forward direction needs EM *)
intros.
apply NNPP; contradict H.
intro d.
apply NNPP; contradict H.
firstorder.
Qed.

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

Theorem or_from_sumbool : forall T, forall p : ( forall s s' : T, { s = s'} + { s <> s' } ),
  forall s s' : T, s = s' \/ s <> s'.
firstorder.
Qed.

Theorem subst_dec' : forall s s' : Substitution,
  s = s' \/ s <> s'.
apply or_from_sumbool.
apply subst_dec.
Qed.

Theorem T_dec' : forall t t' : T,
  t = t' \/ t <> t'.
apply or_from_sumbool.
apply T_dec.
Qed.

Theorem sameThing'' : forall (phi : Formula) (rho : Valuation) ,
  (Satisfies rho phi <-> SatI rho phi) /\ (~ Satisfies rho phi <-> SatNI rho phi).

  induction phi.
  (* equals *)
  intros. rewrite <- SatEquals.
  split; (split; [constructor | inversion 1]; assumption).
  (* and *)
  intros. rewrite <- SatAnd.
  specialize (IHphi1 rho).
  specialize (IHphi2 rho).
  split; (split; [constructor | inversion 1]; tauto).
  (* not *)
  intros. rewrite <- SatNot.
  specialize (IHphi rho).
  split; (split; [constructor | inversion 1];tauto).
  (* forall *)
  intro. rewrite <- SatForall.
  split; (split;[constructor | inversion 1]);try firstorder.
  
  rewrite forall_exists in H.
    destruct H. exists x. firstorder.
Qed.

End FOL.
