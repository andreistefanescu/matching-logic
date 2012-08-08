Module MatchL.

Parameter T : Set.

Parameter M : Set.

Parameter T_dec : forall x y : T, { x = y } + { x <> y }.

Parameter IsVariable : T -> Prop.

Definition Var : Set := { x : T & (IsVariable x) }.

Parameter valuation : Set.

Parameter termToModel : T -> valuation -> M.


Definition Substitution := Var -> T.

Parameter identity : Substitution.

Hypothesis subst_dec : forall s s' : Substitution, { s = s' } + { s <> s' }.

Parameter Apply : Substitution -> T -> T.

Hypothesis identity_refl : forall t, (Apply identity t) = t.

Parameter Update : Substitution -> Var -> T -> Substitution.

Parameter Compose : Substitution -> Substitution -> Substitution.

Inductive Formula : Set :=
  | Equals : T -> T -> Formula
  | And : Formula -> Formula -> Formula
  | Not : Formula -> Formula
  | Forall : Var  -> Formula -> Formula
  | Pattern : T -> Formula.

(* Inductive FOLFormula (Construct : Set) : Set := *)
(*   | UDC : Construct -> FOLFormula Construct *)
(*   | And : FOLFormula Construct -> FOLFormula Construct. *)

(*   | Pattern : T -> Formula. *)
(*   | And : Formula -> Formula -> Formula *)
(*   | Or : Formula -> Formula -> Formula *)
(*   | Implies : Formula -> Formula -> Formula *)
(*   | Exists : Var  -> Formula -> Formula *)


(* x |-> 10     y |-> 11         (x := l, y := l) *)

(* axiom: (l |-> 10, l |-> 11) Implies FFalse *)

(*  | Bool : T -> Formula.

Axiom SatBool : forall gamma : T, forall rho : Valuation, forall t : T,
  (TrueInModel (termToModel rho t))
  <->
  Satisfies gamma rho (Bool t).
*)

(* (* a > 0       gamma,rho |= pattern(a > 0)  *)  *)

  (* | UDP1 : UnaryPredicate -> T -> Formula *)
  (* | UDP2 : BinaryPredicate -> T -> T -> Formula *)

Parameter ApplyF : Substitution -> Formula -> Formula.

Parameter notFree : Var -> Formula -> Prop.

Definition Or phi1 phi2 := (Not (And (Not phi1) (Not phi2))).

Definition Implies phi phi' :=
  (Or (Not phi) phi').

Definition Exists (X : Var) (phi : Formula) :=
  (Not (MatchL.Forall X (Not phi))).

Fixpoint patternless (phi : Formula) : Prop :=
  match phi with
    | Equals _ _ => True
    | And phi1 phi2 => patternless phi1 /\ patternless phi2
    | Not phi' => patternless phi'
    | Forall _ phi' => patternless phi'
    | Pattern _ => False
  end.

Definition Valuation := Substitution.

Definition coerce (v : Var) := projS1 v.

Parameter Satisfies : T -> Valuation -> Formula -> Prop.

Definition Valid phi :=
  forall gamma : T, forall rho : Valuation,
    Satisfies gamma rho phi.

(* gamma, rho |= Equals t t'   iff    rho(t) = rho(t') *)
Axiom SatEquals : forall gamma : T, forall rho : Valuation, forall t t' : T,
  Apply rho t = Apply rho t'
  <->
  Satisfies gamma rho (Equals t t').

(* gamma,rho |= Vx.phi  iff   forall t, gamma,rho[x/t] |= phi *)
Axiom SatForall : forall gamma : T, forall rho : Valuation, forall x : Var, forall phi : Formula,
  (forall t : T, Satisfies gamma (Update rho x t) phi)
  <->
  Satisfies gamma rho (Forall x phi).

(* gamma,rho |= phi /\ phi' iff 
         gamma,rho |= phi and gamma,rho |= phi' *)
Axiom SatAnd : forall gamma : T, forall rho : Valuation, forall phi phi' : Formula,
  (Satisfies gamma rho phi /\ Satisfies gamma rho phi')
  <->
  Satisfies gamma rho (And phi phi').

(* gamma,rho |= not phi  iff
          gamma,rho |= phi does not hold ;-) *)
Axiom SatNot : forall gamma : T, forall rho : Valuation, forall phi : Formula,
  (~Satisfies gamma rho phi)
  <->
  Satisfies gamma rho (Not phi).

(* FOL(=), FOL(=,<,...) *)
(* <a>_heap /\ a > 0 *)
(* gamma, rho |= Pattern t    iff    rho(t) = gamma *)
Axiom SatPattern : forall gamma : T, forall rho : Valuation, forall t : T,
  (gamma = Apply rho t)
  <->
  Satisfies gamma rho (Pattern t).

Hypothesis SatApply : forall gamma rho f subst,
  Satisfies gamma rho (ApplyF subst f) <->
  Satisfies gamma (Compose rho subst) f.

Hypothesis SatExists : forall gamma rho X phi,
  Satisfies gamma rho (Exists X phi) <->
  exists t, Satisfies gamma (Update rho X t) phi.

Hypothesis notFree_sat : forall x f,
  notFree x f ->
  forall gamma rho t,
    Satisfies gamma rho f
    <-> Satisfies gamma (Update rho x t) f.

Fixpoint SatisfiesF (gamma : T) (rho : Valuation) (phi : Formula) : Prop :=
  match phi with
    | Equals t1 t2 => (Apply rho t1 = Apply rho t2)
    | Forall v phi' => forall (s : T), SatisfiesF gamma (Update rho v s) phi'
    | And phi1 phi2 => SatisfiesF gamma rho phi1 /\ SatisfiesF gamma rho phi2
    | Not phi' => ~SatisfiesF gamma rho phi'
    | Pattern t => (gamma = Apply rho t)
  end.

Require Import Setoid.

Theorem sameThing : forall (gamma : T) (rho : Valuation) (phi : Formula),
  SatisfiesF gamma rho phi <-> Satisfies gamma rho phi.
  intros. generalize dependent rho.
  induction phi. intros. apply SatEquals.
  intros. simpl. rewrite IHphi1. rewrite IHphi2. apply SatAnd.
  intros. simpl. rewrite IHphi. apply SatNot.
  intros. simpl. split.
  rewrite <- SatForall. intros. apply IHphi. apply H.
  rewrite <- SatForall. intros. apply IHphi. apply H.
  intros. rewrite <- SatPattern. simpl. reflexivity.
Qed.

Inductive SatI : T -> Valuation -> Formula -> Prop :=
  | SatIEquals : forall gamma : T, forall rho : Valuation, forall t t' : T,
                  (Apply rho t = Apply rho t') ->
                    SatI gamma rho (Equals t t')
  | SatIForall : forall gamma : T, forall rho : Valuation, forall x : Var, forall phi : Formula,
                  (forall t : T, SatI gamma (Update rho x t) phi) ->
                        SatI gamma rho (Forall x phi)
  | SatIAnd : forall gamma : T, forall rho : Valuation, forall phi phi' : Formula,
               SatI gamma rho phi ->
                 SatI gamma rho phi' ->
                   SatI gamma rho (And phi phi')
  | SatINot : forall gamma : T, forall rho : Valuation, forall phi : Formula,
               (SatNI gamma rho phi) ->
                 SatI gamma rho (Not phi)
  | SatIPattern : forall gamma : T, forall rho : Valuation, forall t : T,
               gamma = Apply rho t ->
                 SatI gamma rho (Pattern t)
with SatNI : T -> Valuation -> Formula -> Prop :=
  | SatNIEquals : forall gamma : T, forall rho : Valuation, forall t t' : T,
                  (Apply rho t <> Apply rho t') ->
                    SatNI gamma rho (Equals t t')
  | SatNIForall : forall gamma : T, forall rho : Valuation, forall x : Var, forall phi : Formula,
    (exists t : T, SatNI gamma (Update rho x t) phi) -> SatNI gamma rho (Forall x phi)
  | SatNIAnd : forall gamma : T, forall rho : Valuation, forall phi phi' : Formula,
               (SatNI gamma rho phi \/ SatNI gamma rho phi') ->
                   SatNI gamma rho (And phi phi')
  | SatNINot : forall gamma : T, forall rho : Valuation, forall phi : Formula,
               (SatI gamma rho phi) ->
                 SatNI gamma rho (Not phi)
  | SatNIPattern : forall gamma : T, forall rho : Valuation, forall t : T,
               gamma <> Apply rho t ->
                 SatNI gamma rho (Pattern t).

Require Import Classical.

Theorem EM : forall (p : Prop), p \/ ~ p.
  intros.
  tauto.
Qed.

Theorem forall_exists : forall D, forall P : D -> Prop,
  ~ (forall d : D, P d) <-> exists d : D, ~ P d.
split.
intros.
apply Peirce.
intros.
unfold not in H.
exfalso.
apply H.
intros.
apply Peirce.
intros.
exfalso.
apply H0.
exists d.
assumption.
intros.
unfold not.
intros.
elim H.
intros.
assert (P x).
apply H0.
contradiction.
Qed.

Theorem forall_exists' : forall D, forall P : D -> Prop,
  ~ (forall d : D, ~ P d) <-> exists d : D, P d.
split.
intros.
apply Peirce.
intros.
unfold not in H.
exfalso.
apply H.
intros.
apply Peirce.
intros.
exfalso.
apply H0.
exists d.
assumption.
intros.
unfold not.
intros.
elim H.
intros.
assert (P x).
assumption.
eapply H0.
apply H1.
Qed.

Theorem or_from_sumbool : forall T, forall p : ( forall s s' : T, { s = s'} + { s <> s' } ),
  forall s s' : T, s = s' \/ s <> s'.
intros.
remember (p s s') as q.
inversion q; auto.
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

Ltac split3 :=
  match goal with
    | [ |- ?X /\ ?Y /\ ?Z ] => split; [ | split ]
  end.

Ltac destruct_ands :=
  repeat match goal with
    | [ H : ?P /\ ?Q |- _ ] => decompose [and] H; clear H
    | [ H : ?P <-> ?Q |- _ ] => unfold iff in H; decompose [and] H; clear H
  end.

Ltac destruct_sat :=
  match goal with
    | [ H : SatI ?P ?Q (?R _ _) |- _ ] => inversion H; clear H
    | [ H : SatNI ?P ?Q (?R _ _) |- _ ] => inversion H; clear H
  end.

Theorem sameThing'' : forall (gamma : T) (rho : Valuation) (phi : Formula),
  (Satisfies gamma rho phi <-> SatI gamma rho phi) /\
  (~ Satisfies gamma rho phi <-> SatNI gamma rho phi) /\
  (Satisfies gamma rho phi \/ ~Satisfies gamma rho phi).
  Hint Extern 1 (SatI ?P ?Q ?R) => constructor; auto.
  Hint Extern 1 (SatNI ?P ?Q ?R) => constructor; auto.
  Hint Extern 1 (Satisfies _ _ _) => destruct_sat; auto.

  intros. generalize dependent rho.

  induction phi; intros; [ rewrite <- SatEquals | rewrite <- SatAnd |
    rewrite <- SatNot | rewrite <- SatForall | rewrite <- SatPattern ].

  (* equals *)
  split3;
  [ split; [ constructor | inversion 1 ]; tauto |
    split; [ constructor | inversion 1 ]; tauto |
    tauto ].
 
  (* and *)
  specialize (IHphi1 rho).
  specialize (IHphi2 rho).
  destruct_ands.
  split3;
  [ split; [ constructor | inversion 1 ]; tauto |
    split; [ constructor | inversion 1 ]; tauto |
    tauto ].

  (* not *)
  specialize (IHphi rho).
  destruct_ands.
  split3; 
  [ split; [ constructor | inversion 1 ]; tauto |
    split; [ constructor | inversion 1 ]; tauto |
    tauto ].

  (* forall *)
  split3.
  split.
  constructor. intros. specialize (H t). specialize (IHphi (Update rho v t)). tauto.
  inversion 1. intros. specialize (H3 t). specialize (IHphi (Update rho v t)). tauto.
  split.
  constructor. intros. rewrite forall_exists in H. firstorder.
  inversion 1. intros. rewrite forall_exists. firstorder.
  tauto.

  (* pattern *)
  split3; [
  split; [ constructor | inversion 1]; tauto |
  split; [ constructor | inversion 1]; tauto |
  tauto].
Qed.

End MatchL.
