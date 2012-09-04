Require Import List.
Require Import matchingl.

Require Import reduction.

Set Implicit Arguments.

Module MatchLReduction(Base : ObjectLanguage).

Export Base.
Export reduction.

Definition Rule := (Formula * Formula)%type.

Definition System := Rule -> Prop.
Definition rules_system l : System := fun r => In r l.

Definition cons_System : Rule -> System -> System :=
  fun r S r' => r' = r \/ S r'.

Definition wd_rule (r : Rule) :=
  forall gamma : M, forall rho : Valuation,
    Satisfies gamma rho (fst r) ->
      exists gamma', Satisfies gamma' rho (snd r).

Definition wd_system (s : System) :=
  forall r : Rule,
    s r -> wd_rule r.

Definition ts (s : System) (gamma : M) (gamma' : M) :=
  exists r : Rule, exists rho : Valuation,
    (s r /\ Satisfies gamma rho (fst r)  /\ Satisfies gamma' rho (snd r)).

Require Import Relation_Definitions.
Require Import Relation_Operators.

(*** SEMANTIC ENTAILMENT OF REWRITE RULES BY TRANSITION SYSTEM ***)

(* S |= phi => phi'               entails S (phi, phi') *)
Definition entails (strict : bool) (s : relation M) (r : Rule) :=
  forall gamma : M,
    terminates gamma s ->
      forall rho : Valuation,
        Satisfies gamma rho (fst r) ->
          exists gamma' : M,
            (clos s strict gamma gamma'
              /\ Satisfies gamma' rho (snd r)).

Definition entails_system strict S (S' : System) :=
  forall r, S' r -> entails strict S r.

(* Weakening lemma *)
Lemma ts_weaken S (r : Rule) (gamma gamma' : M) :
  ts (rules_system S) gamma gamma'
  -> ts (rules_system (r :: S)) gamma gamma'.
Proof. firstorder. Qed.  

Lemma terminates_weaken S (r : Rule) (gamma : M) :
  terminates gamma (ts (rules_system (r :: S)))
  -> terminates gamma (ts (rules_system S)).
Proof.
  apply Acc_weaken; auto using ts_weaken.
Qed.

Lemma entails_weaken (R1 R2 : relation M)
  (HWeak : forall a b, R1 a b -> R2 a b)
  strict (r : Rule) :
  entails strict R1 r -> entails strict R2 r.
Proof.
  unfold entails. intros.
  destruct H with gamma rho.
  revert H0; apply Acc_weaken. auto.
  auto.
  exists x.
  intuition.
  revert H3.
  apply clos_weaken.
  auto.
Qed.

Lemma entails_system_weaken (R1 R2 : relation M)
  (HWeak : forall a b, R1 a b -> R2 a b)
  strict (S : System) :
  entails_system strict R1 S -> entails_system strict R2 S.
Proof.
  unfold entails_system.
  eauto using entails_weaken.
Qed.

Lemma wd_proper_refl (A : System) :
  wd_system A -> entails_system true (ts A) A.
Proof.
  unfold wd_system, entails_system.

  intros. specialize (H r H0).

  unfold entails; unfold wd_rule in H.
  intros.
  specialize (H gamma rho H2).
  destruct H.
  exists x.

  split.

  apply clos_step.
  exists r. exists rho.
  tauto.
  tauto.
Qed.

End MatchLReduction.