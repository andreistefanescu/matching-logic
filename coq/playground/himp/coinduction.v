Set Implicit Arguments.

Require Import domains.
Require Import kstyle.

CoInductive reaches (x : kcfg) (P : kcfg -> Prop) : Prop :=
  | done : P x -> reaches x P
  | step : forall y, kstep x y -> reaches y P -> reaches x P
  .

Definition steps x y := reaches x (kequiv y).

Definition RRel : Type := kcfg -> (kcfg -> Prop) -> Prop.
Definition subrel (kcfg B : RRel) : Prop := forall x P, kcfg x P -> B x P.

Definition sound (X : RRel) : Prop := subrel X reaches.

(* Base functor of the path predicate *)
Inductive stepF (X : RRel) (x : kcfg) (P : kcfg -> Prop) : Prop :=
  | DoneF : P x -> stepF X x P
  | StepF : forall y, kstep x y -> X y P -> stepF X x P.

Definition stable (X : RRel) : Prop := subrel X (stepF X).

CoFixpoint stable_sound X (Hstable : stable X) : sound X :=
  fun x P HxP =>
  match Hstable _ _ HxP with
  | DoneF Px => done _ _ Px
  | StepF y Rxy XyP => step Rxy (@stable_sound _ Hstable _ _ XyP)
  end.

Definition F_stable (F : RRel -> RRel) (X : RRel) : Prop := subrel X (stepF (F X)).

(* Direct version of transitivity *)
Inductive trans (X : RRel) (x : kcfg) (P : kcfg -> Prop) : Prop :=
  | tleaf : X x P -> trans X x P
  | tdone : P x -> trans X x P
  | tstep : forall y, kstep x y -> trans X y P -> trans X x P
  | ttrans : forall Q, trans X x Q -> (forall y, Q y -> trans X y P) -> trans X x P
  .

Lemma trans_derived (X : RRel) (trans_stable : F_stable trans X) : stable (trans X).
unfold stable.
induction 1;eauto using stepF.
destruct IHtrans; eauto using StepF,ttrans.
Qed.

Definition trans_sound (X : RRel) (trans_stable : F_stable trans X) : sound X :=
  fun x y Hxy => stable_sound (trans_derived trans_stable) _ _ (tleaf _ _ _ Hxy).

(* some tactics for execution
*)