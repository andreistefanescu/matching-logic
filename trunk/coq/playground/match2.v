(* trying hoas *)

Module MatchingLogic.

Parameter T : Set.

Parameter T_dec : forall x y : T,
  {x = y} + {x <> y}.

Parameter IsVariable : T -> Prop. (* Checks if a member of T is a variable *)

Definition Var : Set := {x : T & (IsVariable x)}.

Definition Substitution := Var -> T.

Parameter Apply : Substitution -> T -> T.

Parameter Update : Substitution -> Var -> T -> Substitution.

Inductive Formula : Set :=
  | Equals : T -> T -> Formula
  | Forall : (Var -> Formula) -> Formula
  | And : Formula -> Formula -> Formula
(*  | Not : Formula -> Formula *)
  | Pattern : T -> Formula.

Definition Valuation := Substitution.

Definition coerce (v : Var) := projS1 v.

Inductive Satisfies : T -> Valuation -> Formula -> Prop :=
  | SatEquals : forall gamma : T, forall rho : Valuation, forall t t' : T,
                  (Apply rho t = Apply rho t') ->
                    Satisfies gamma rho (Equals t t')
  | SatForall : forall gamma : T, forall rho : Valuation, forall x : Var, forall phi : Formula,
                  (forall rho' : Valuation,
                    (forall y : Var, y <> x -> (Apply rho (coerce y) = Apply rho' (coerce y))) ->
                      Satisfies gamma rho' phi) ->
                        Satisfies gamma rho (Forall x phi)
  | SatAnd : forall gamma : T, forall rho : Valuation, forall phi phi' : Formula,
               Satisfies gamma rho phi ->
                 Satisfies gamma rho phi' ->
                   Satisfies gamma rho (And phi phi')
(*  | SatNot : forall gamma : T, forall rho : Valuation, forall phi : Formula,
               (~Satisfies gamma rho phi) ->
                 Satisfies gamma rho (Not phi) *)
  | SatPattern : forall gamma : T, forall rho : Valuation, forall pi : T,
                   gamma = Apply rho pi ->
                     Satisfies gamma rho (Pattern pi).

Definition RewriteRule := (Formula * Formula)%type.

Require Import List.
Require Import ListSet.

Definition RewriteSystem := set RewriteRule.

Print RewriteSystem.
Print ListSet.
Check set_mem.

SearchAbout sumbool.

Theorem FormulaDecidable : forall x y : Formula,
  {x = y} + {x <> y}.
intros.
destruct x, y.
destruct (T_dec t t1), (T_dec t0 t2).
rewrite e.
rewrite e0.
apply left.
reflexivity.
apply right.
unfold not.
intros.
inversion H.
rewrite H2 in n.
unfold not in n.
apply n.
reflexivity.
Admitted.

Theorem RewriteRuleDecidable : forall x y : RewriteRule,
  {x = y} + {x <> y}.
intros.
destruct x, y.
destruct (FormulaDecidable f f1).
destruct (FormulaDecidable f0 f2).
apply left.
Admitted.

Definition Transition (rs : RewriteSystem) (gamma gamma' : T) :=
  exists phi : Formula, 
    exists phi' : Formula,
      exists rho : Valuation,
        set_mem RewriteRuleDecidable (pair phi phi') rs = true /\
        Satisfies gamma rho phi /\
        Satisfies gamma' rho phi'.

Require Import Relation_Definitions.
Require Export Relation_Operators.
Require Export Wf.

Definition rs : RewriteSystem.
Admitted.

Check (Transition rs).
Check clos_refl_trans.

Definition TransitionStar (rs : RewriteSystem) :=
  clos_refl_trans T (Transition rs).

Check (TransitionStar rs).

Definition Terminates (rs : RewriteSystem) (gamma : T) :=
  well_founded (TransitionStar rs).

Definition Entails (rs : RewriteSystem) (phi phi' : Formula) :=
  forall gamma : T,
    Terminates rs gamma ->
    forall rho : Valuation,
      Satisfies gamma rho phi ->
      (exists gamma' : T,
        TransitionStar rs gamma gamma' /\
        Satisfies gamma' rho phi').

Fixpoint ApplyF (rho : Substitution) (phi : Formula) : Formula :=
  match phi with
    | Equals t t' => Equals (Apply rho t) (Apply rho t')
  end

(* Inductive Formula : Set := *)
(*   | Equals : T -> T -> Formula *)
(*   | Forall : Var -> Formula -> Formula *)
(*   | And : Formula -> Formula -> Formula *)
(* (*  | Not : Formula -> Formula *) *)
(*   | Pattern : T -> Formula. *)

Inductive PS : RewriteSystem -> Formula -> Formula -> Prop :=
  | ps_refl :
    forall phi : Formula, forall A : RewriteSystem, PS A phi phi
  | ps_axiom :
    forall A : RewriteSystem, forall phi phi' : Formula,
      set_mem RewriteRuleDecidable (phi, phi') A = true ->
      PS A phi phi'
  | ps_subst :
    forall A : RewriteSystem, forall phi phi' : Formula,
      set_mem RewriteRuleDecidable (phi, phi') A = true ->
      forall rho : Valuation,
        PS A (Apply rho phi) (Apply rho phi').
