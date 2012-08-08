Module MatchLReduction.

Require Import List.
Require Import matchingl.
Import MatchL.

Parameter t : T.

Definition x := (MatchL.Pattern t).

Definition Rule := (Formula * Formula)%type.

Definition System := list Rule.

Definition ts (s : System) (gamma : T) (gamma' : T) :=
  exists r : Rule, exists rho : Substitution,
    (In r s /\ Satisfies gamma rho (fst r)  /\ Satisfies gamma' rho (snd r)).

Inductive terminates (gamma : T) (s : System) : Prop :=
  | terminates_intro :
    (forall gamma', ts s gamma gamma' -> terminates gamma' s) -> terminates gamma s.

Definition wd_rule (r : Rule) :=
  forall gamma : T, forall rho : Substitution,
    Satisfies gamma rho (fst r) ->
      exists gamma', Satisfies gamma' rho (snd r).

Definition wd_system (s : System) :=
  forall r : Rule,
    In r s -> wd_rule r.

Require Import Relation_Definitions.
Require Import Relation_Operators.

(*** TRANZITIVE(-REFLEXIVE) CLOSURES ***)

Definition star := clos_refl_trans T.

Definition tranz := clos_trans T.

Theorem tranz_to_star : forall R gamma gamma',
  tranz R gamma gamma' -> star R gamma gamma'.
intros.
induction H.
constructor; assumption.
eapply rt_trans.
eassumption.
eassumption.
Qed.

(*** SEMANTIC ENTAILMENT OF REWRITE RULES BY REWRITE SYSTEM ***)

(* S |= phi => phi'               entails S (phi, phi') *)
Definition entails (s : System) (r : Rule) :=
  forall gamma : T,
    terminates gamma s ->
      forall rho : Substitution,
        Satisfies gamma rho (fst r) ->
          exists gamma' : T,
            (star (ts s) gamma gamma' /\ Satisfies gamma' rho (snd r)).

Definition entails_proper (s : System) (r : Rule) :=
  forall gamma : T,
    terminates gamma s ->
      forall rho : Substitution,
        Satisfies gamma rho (fst r) ->
          exists gamma' : T,
            (tranz (ts s) gamma gamma' /\ Satisfies gamma' rho (snd r)).

(*** TERMINATION OF gamma IN A REWRITE SYSTEM ***)

(* gamma terminates in at most (n-1) steps *)
Fixpoint nterminates_gen (n : nat) (gamma : T) (A : System) : Prop :=
  match n with
    | 0 => False
    | S n' => 
      forall gamma',
        ts A gamma gamma' -> 
        nterminates_gen n' gamma' A
  end.

Require Import Arith.

Theorem nterminates_weaken : forall n gamma gamma' A,
  nterminates_gen n gamma A ->
  (ts A) gamma gamma' ->
  nterminates_gen (n - 1) gamma' A.
intros.
destruct n as [ | n' ].
inversion H.
simpl. rewrite <- minus_n_O.
simpl in H. apply H.
apply H0.
Qed.

Theorem nterminates_monotone : forall n gamma A, nterminates_gen n gamma A ->
  nterminates_gen (S n) gamma A.

induction n.
intros; inversion H.
remember (S n) as nn.
intros.
simpl.
intros.
assert (nterminates_gen (nn - 1) gamma' A).
eapply nterminates_weaken.
apply H.
apply H0.
rewrite Heqnn in H1.
simpl in H1.
rewrite <- minus_n_O in H1.
replace (n + 1) with nn in IHn.
apply IHn.
assumption.
rewrite Heqnn.
rewrite <- plus_n_Sm.
rewrite <- plus_n_O.
reflexivity.
Qed.

Theorem nterminates_gen_star : forall n gamma gamma' A,
  star (ts A) gamma gamma' ->
  nterminates_gen n gamma A ->
  nterminates_gen n gamma' A.
   induction 1.
   (* step *)
   intros. destruct n. inversion H0.
   apply nterminates_monotone.
   apply H0. assumption.
   (* refl *) 
   trivial.
   (* trans *)
   intros.
   apply (IHclos_refl_trans2 (IHclos_refl_trans1 H1)).
Qed.

Theorem nterminates_gen_tranz : forall n gamma gamma' A,
  tranz (ts A) gamma gamma' ->
  nterminates_gen n gamma A ->
  nterminates_gen n gamma' A.
   intros.
   eapply nterminates_gen_star.
   apply tranz_to_star.
   apply H.
   assumption.
Qed.

(*** n-SOUNDNESS OF REWRITE RULES ***)

Definition nsound_rule_gen (n : nat) (A : System) (phi phi' : Formula) :=
  forall gamma : T, 
    nterminates_gen n gamma A ->
    forall rho : Valuation,
      Satisfies gamma rho phi ->
      exists gamma',
        (star (ts A) gamma gamma' /\ Satisfies gamma' rho phi').

Definition nsound'_rule_gen (n : nat) (A : System) (r : Rule) :=
  nsound_rule_gen n A (fst r) (snd r).

Definition nproper_rule_gen (n : nat) (A : System) (phi phi' : Formula) :=
  forall gamma : T, 
    nterminates_gen n gamma A ->
    forall rho : Valuation,
      Satisfies gamma rho phi ->
      exists gamma',
        (tranz (ts A) gamma gamma' /\ Satisfies gamma' rho phi').

Definition nproper'_rule_gen (n : nat) (A : System) (r : Rule) :=
  nproper_rule_gen n A (fst r) (snd r).

Definition sound_rule_gen (A : System) (phi phi' : Formula) :=
  entails A (phi, phi').

Definition sound'_rule_gen (A : System) (r : Rule) :=
  sound_rule_gen A (fst r) (snd r).

Definition proper_rule_gen (A : System) (phi phi' : Formula) :=
  entails_proper A (phi, phi').

Definition proper'_rule_gen (A : System) (r : Rule) :=
  proper_rule_gen A (fst r) (snd r).

Definition proper_system_gen (A : System) (A' : System) :=
  @List.Forall Rule (proper'_rule_gen A') A.

Lemma terminates_exists : forall gamma A,
   terminates gamma A <-> exists n, nterminates_gen n gamma A.
admit.
Qed.

Lemma sound_forall_nsound :
  forall A phi phi',
    sound_rule_gen A phi phi' <-> (forall n : nat, nsound_rule_gen n A phi phi').
split.

intro.
unfold sound_rule_gen in H.
unfold entails in H.
intros.
unfold nsound_rule_gen.
intros.
apply H.
apply terminates_exists.
exists n; assumption.
simpl.
assumption.

unfold sound_rule_gen.
unfold nsound_rule_gen.
unfold entails.
intros.
simpl.
rewrite terminates_exists in H0.
destruct H0.
specialize (H x0 gamma).
apply H.
assumption.
assumption.
Qed.

Lemma proper_forall_nproper :
  forall A phi phi',
    proper_rule_gen A phi phi' <-> (forall n : nat, nproper_rule_gen n A phi phi').
split.

intro.
unfold proper_rule_gen in H.
unfold entails in H.
intros.
unfold nproper_rule_gen.
intros.
apply H.
apply terminates_exists.
exists n; assumption.
simpl.
assumption.

unfold proper_rule_gen.
unfold nproper_rule_gen.
unfold entails_proper.
intros.
simpl.
rewrite terminates_exists in H0.
destruct H0.
specialize (H x0 gamma).
apply H.
assumption.
assumption.
Qed.

Definition nsound_system_gen (n : nat) (A : System) (A' : System) : Prop :=
  @List.Forall Rule (nsound'_rule_gen n A') A.

Definition nproper_system_gen (n : nat) (A : System) (A' : System) : Prop :=
  @List.Forall Rule (nproper'_rule_gen n A') A.

Lemma nproper_rule_gen_iff_nproper'_rule_gen : forall n phi phi' A,
  nproper_rule_gen n A phi phi' <-> nproper'_rule_gen n A (phi, phi').
intros.
unfold nproper'_rule_gen.
simpl.
apply iff_refl.
Qed.

Lemma proper_rule_gen_iff_proper'_rule_gen : forall phi phi' A,
  proper_rule_gen A phi phi' <-> proper'_rule_gen A (phi, phi').
intros.
unfold proper'_rule_gen.
simpl.
apply iff_refl.
Qed.

Lemma nsound_rule_gen_iff_nsound'_rule_gen : forall n phi phi' A,
  nsound_rule_gen n A phi phi' <-> nsound'_rule_gen n A (phi, phi').
intros.
unfold nsound'_rule_gen.
simpl.
apply iff_refl.
Qed.

Lemma sound_rule_gen_iff_sound'_rule_gen : forall phi phi' A,
  sound_rule_gen A phi phi' <-> sound'_rule_gen A (phi, phi').
intros.
unfold sound'_rule_gen.
simpl.
apply iff_refl.
Qed.

Lemma proper_system_forall_nproper_system :
  forall A A',
    proper_system_gen A A' <-> (forall n : nat, nproper_system_gen n A A').
intros.
unfold proper_system_gen.
unfold nproper_system_gen.
induction A.
split; constructor.
split; constructor.
inversion H.
destruct a.
rewrite <- proper_rule_gen_iff_proper'_rule_gen in H2.
rewrite <- nproper_rule_gen_iff_nproper'_rule_gen.
generalize dependent n.
apply proper_forall_nproper; assumption.
apply IHA. inversion H. assumption.
destruct a.
rewrite <- proper_rule_gen_iff_proper'_rule_gen.
apply proper_forall_nproper.
intros n.
specialize (H n).
inversion H.
assumption.
assert (Hm : forall n : nat, List.Forall (nproper'_rule_gen n A') A).
intros.
specialize (H n).
inversion H.
assumption.
apply IHA.
assumption.
Qed.

(*** for a fixed system SF ***)

Hypothesis SF : System.

Definition nsound_system (n : nat) (A : System) : Prop := 
  nsound_system_gen n A SF.

Definition nproper_system (n : nat) (A : System) : Prop := 
  nproper_system_gen n A SF.

Definition nproper_rule n phi phi' := nproper_rule_gen n SF phi phi'.

Definition proper_rule phi phi' := proper_rule_gen SF phi phi'.

Definition nproper'_rule n r := nproper_rule n (fst r) (snd r).

Definition nsound_rule n phi phi' := nsound_rule_gen n SF phi phi'.

Definition nsound'_rule n r := nsound_rule n (fst r) (snd r).

Definition proper_system (A : System) :=
  proper_system_gen A SF.

Lemma nproper_rule_iff_nproper'_rule : forall n phi phi',
  nproper_rule n phi phi' <-> nproper'_rule n (phi, phi').
intros.
unfold nproper'_rule.
simpl.
apply iff_refl.
Qed.

Lemma nsound_rule_iff_nsound'_rule : forall n phi phi',
  nsound_rule n phi phi' <-> nsound'_rule n (phi, phi').
intros.
unfold nsound'_rule.
simpl.
apply iff_refl.
Qed.

End MatchLReduction.
