Require Import ZArith.
Require Import List.
Require Import FMapPositive.
Require Import String.
Open Scope string_scope.

Require Import domains.

Lemma eval_happy : forall env,
  steps (KCfg (kra (SAssign "x" (EPlus (EVar "x") (EVar "y"))) nil)
            (env :* "x" |-> 12%Z :* "y" |-> 13%Z) mapEmpty mapEmpty)
        (KCfg nil (env :* "x" |-> 25%Z :* "y" |-> 13%Z) mapEmpty mapEmpty).
intros.
repeat (refine (more _ (@kequiv_refl _) _ _);[econstructor (reflexivity || find_map_entry)|]);
simpl Zplus; finish.
Qed.

(* Try "quote" on the env *)
(* Use a mixed coinductive sequencing to use loop invariants? *)

Lemma eval_happy' : forall env,
  steps (KCfg (kra (SAssign "x" (EPlus (EVar "x") (EVar "y"))) nil)
            ("x" |-> 12%Z :* "y" |-> 13%Z :* env) mapEmpty mapEmpty)
        (KCfg nil ("x" |-> 25%Z :* "y" |-> 13%Z :* env) mapEmpty mapEmpty).
intros;
repeat (refine (more _ (@kequiv_refl _) _ _);[match goal with [|- kstep ?l _] => eapply (eval_sound l) end|]);
simpl Zplus; finish.
Qed.

Lemma loop_test':
  steps (KCfg (kra (SWhile (BLe (ECon 0) (EVar "x"))
    (SAssign "x" (EPlus (EVar "x") (ECon (-1)%Z))))
  nil) ("x" |-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" |-> (-1)%Z) mapEmpty mapEmpty).
Proof.
Ltac step_eval :=refine (more _ (@kequiv_refl _) _ _);[match goal with [|- kstep ?l _] => eapply (eval_sound l) end|].
intros;repeat step_eval;simpl;finish.
Qed.

Function evals n kcfg :=
  match n with
    | 0 => kcfg
    | S n => 
      match eval kcfg with
      | Some kcfg' => evals n kcfg'
      | None => kcfg
     end
  end.
Lemma evals_sound :
  forall n c1 c2,
    kequiv (evals n c1) c2 -> steps c1 c2.
Proof.
induction n; simpl; intros c1 c2.
apply done.
pose proof (eval_sound c1).
destruct (eval c1).
intro.
apply more with c1 k. reflexivity.
assumption. apply IHn. assumption.
apply done.
Qed.

Lemma loop_test'':
  steps (KCfg (kra (SWhile (BLe (ECon 0) (EVar "x"))
    (SAssign "x" (EPlus (EVar "x") (ECon (-1)%Z))))
  nil) ("x" |-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" |-> (-1)%Z) mapEmpty mapEmpty).
Proof.
intros;apply (evals_sound 1000);lazy;repeat (apply conj);[reflexivity|simpl;equate_maps ..].
Qed.

Lemma loop_test:
  steps (KCfg (kra (SWhile (BLe (ECon 0) (EVar "x"))
    (SAssign "x" (EPlus (EVar "x") (ECon (-1)%Z))))
  nil) ("x" |-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" |-> (-1)%Z) mapEmpty mapEmpty).
Proof.
intros;
repeat (refine (more _ (@kequiv_refl _) _ _);[econstructor (reflexivity || find_map_entry)|];instantiate;simpl Zplus);
finish.
Qed.

CoFixpoint sum :
  forall (x y z : Z) erest env heap labels,
    (0 <= x)%Z ->
    z = (x + y)%Z ->
    env ~= ("i" |-> x :* "j" |-> y :* erest) ->
  steps
    (KCfg (kra (SWhile (BLe (ECon 1%Z) (EVar "i"))
                       (Seq
                          (SAssign "i" (EPlus (EVar "i") (ECon (-1)%Z)))
                          (SAssign "j" (EPlus (EVar "j") (ECon 1%Z)))))
               kdot)
                env heap labels)
    (KCfg kdot
          ("i" |-> 0%Z :* "j" |-> z%Z :* erest) heap labels).
intros;step_rule;run_circ sum.
Qed.

Coercion EVar : string >-> Exp.

Definition gcdProg : Map string Stmt :=
  "gcd" |->
        SIf (BLe "a" "b")
          (SIf (BLe "b" "a")
               (Jump "done")
               (Seq (SAssign "b" (EMinus "b" "a"))
                    (Jump "gcd")))
          (Seq (SAssign "a" (EMinus "a" "b"))
               (Jump "gcd")).
Lemma label_eval : forall env,
  steps (KCfg (kra (Jump "gcd") kdot)
            ("a" |-> 12%Z :* "b" |-> 13%Z :* env) mapEmpty gcdProg)
        (KCfg (kra (Jump "done") kdot)
             ("a" |-> 1%Z :* "b" |-> 1%Z :* env) mapEmpty gcdProg).
intros. apply evals_sound with 307; simpl; repeat split; reflexivity.
Qed.
