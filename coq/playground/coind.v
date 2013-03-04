Generalizable Variables R.

Class Impl (R : Type) : Type :=
  implies : R -> R -> Prop.
Instance prop_impl : Impl Prop : Type :=
  {implies := fun x y => x -> y}.
Instance lift_impl X `(IR : Impl R) : Impl (X -> R) :=
  {implies := fun x y => forall (v : X), implies (x v) (y v)}.

Definition closed `(Impl R) (K : R -> R) (P : R) : Prop := implies (K P) P.
Definition stable `(Impl R) (K : R -> R) (P : R) : Prop := implies P (K P).

(* If G includes every K-stable set, then G includes the gfp of K *)
Definition includesGFP `(Impl R) (K : R -> R) (G : R) : Prop :=
  forall (D : R), stable implies K D -> implies D G.

Module Type TransitionSystem.
Parameter domain : Set.
Parameter R : domain -> domain -> Prop.
End TransitionSystem.

Module Coinductive (TS : TransitionSystem).
Import TS.
Definition spec := domain -> Prop.

Definition ntForall {A : Type} (pred : A -> Prop) (body : A -> Prop) :=
  (exists (a : A), pred a) /\ (forall (a : A), pred a -> body a).

(* Coinductive reachability relation *)
CoInductive reaches (x : domain) (P : spec) : Prop :=
  | done : P x -> reaches x P
  | step : ntForall (R x) (fun y => reaches y P) -> reaches x P.

(* Base functor of reachability relation *)
Inductive reachBase (X : domain -> spec -> Prop) (x : domain) (P : spec) : Prop :=
  | b_done : P x -> reachBase X x P
  | b_step : ntForall (R x) (fun y => X y P) -> reachBase X x P.

(* Show that reaches is actually the greatest fixpoint of the reachability relation *)
Lemma reaches_stable : implies reaches (reachBase reaches).
Proof. destruct 1; constructor(assumption). Qed.

Lemma reaches_greatest : includesGFP _ reachBase reaches.
Proof.
unfold includesGFP, lift_impl, prop_impl, stable, implies.
intros until 1.
cofix.
intros.
specialize (H v v0 H0).
destruct H.
apply done;assumption.
apply step; unfold ntForall in * |- *; intuition.
Qed.

(* The transitivty proof rule *)                                      
Inductive transRule (X : domain -> spec -> Prop) (x : domain) (P : spec) : Prop :=
  | trans : forall Q, X x Q -> (forall y, Q y -> X y P) -> transRule X x P.

(* Show that it's sound for reachability *)
Lemma transSound : closed _ transRule reaches.
unfold closed, lift_impl, prop_impl, implies.
intros.
destruct H.
revert v H H0.
cofix.
destruct 1;[clear transSound|intros;apply step;unfold ntForall in *|- *];
intuition.
Qed.

(* Now, we want to show that it's enough to show a relation D is closed
   if we can reduce back to D by aplying base/trans lots of times *)

Inductive steps (D : domain -> spec -> Prop) (x : domain) (P : spec) : Prop :=
  | fromD : D x P -> steps D x P
  | byReach : reachBase (steps D) x P -> steps D x P
  | byTrans : forall Q, steps D x Q -> (forall y, Q y -> steps D y P) -> steps D x P.

Lemma distribution : forall (D : domain -> spec -> Prop) x P,
  transRule (reachBase (steps D)) x P -> reachBase (transRule (steps D)) x P.
intros.
destruct H.
destruct H.
(* first was a refl step *)
specialize (H0 _ H).
destruct H0.
(* second was also refl *)
apply b_done. assumption.
(* second was step *)
apply b_step.
unfold ntForall in * |- *. intuition.
apply trans with (eq a).
apply byReach. constructor(reflexivity).
intros. subst y. auto.
(* first side of trans took a step. *)
apply b_step.
unfold ntForall in * |- *. intuition.
apply trans with Q.
auto.
intros.
eauto using steps.
Qed.

Lemma enrich : forall (D : domain -> spec -> Prop),
  implies D (reachBase (steps D)) -> implies (steps D) (reachBase (steps D)).
intros.
intro x. intro P. intro H0.
induction H0.
+ (* Is exactly a D *)
  exact (H _ _ H0).
+ (* was reachBase *)
  assumption.
+ (* first step was trans *)
  destruct IHsteps;[solve[auto]|].
  apply b_step.
  unfold ntForall in H3 |- *.
  intuition.
  eapply byTrans; auto.
Qed.

Lemma reasoning : forall (D : domain -> spec -> Prop),
  implies D (reachBase (steps D)) -> implies D reaches.
Proof.
intros.
apply enrich in H.
apply reaches_greatest in H.
intro; intro; intro.
apply H. apply fromD. assumption.
Qed.
End Coinductive.

Module ExampleRel <: TransitionSystem.

Inductive states : Set :=
  | Start
  | Loop1
  | Loop1Past
  | Loop1Body
  | Mid
  | Loop2
  | Loop2Past
  | Loop2Body
  | FinishA
  | FinishB.

Inductive adv : states -> states -> Prop :=
  | s1 : adv Start Loop1
  | l1t : adv Loop1 Loop1Body
  | l1f : adv Loop1 Loop1Past
  | l1b : adv Loop1Body Loop1
  | m1 : adv Loop1Past Mid
  | m2 : adv Mid Loop2
  | l2t : adv Loop2 Loop2Body
  | l2f : adv Loop2 Loop2Past
  | l2b : adv Loop2Body Loop2
  | fa : adv Loop2Past FinishA
  | fb : adv Loop2Past FinishB
  .

Definition domain := states.
Definition R := adv.
End ExampleRel.
Import ExampleRel.

Definition G x := x = FinishA \/ x = FinishB.
Inductive D : states -> (states -> Prop) -> Prop :=
  | goal : D Start G
  | inv1 : D Loop1 (eq Loop1Past)
  | inv2 : D Loop2 (eq Loop2Past)
  .

Module ExamplePS := Coinductive ExampleRel.
Import ExamplePS.

Ltac base_step := (apply b_step;split;[eexists;constructor|inversion 1;subst]).
Ltac step_step := apply byReach;base_step.
Ltac circ_step := eapply byTrans;[apply fromD;constructor|instantiate;intros;subst].
Ltac done_step := apply byReach;apply b_done;solve[firstorder].
Ltac run := repeat (circ_step || done_step || step_step).

Lemma foo : reaches Start G.
apply (reasoning D);[|constructor].
intro x; intro P; intro H.
destruct H;base_step;run.
Qed.