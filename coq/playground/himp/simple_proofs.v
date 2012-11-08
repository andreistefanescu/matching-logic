Require Import ZArith.
Require Import List.
Require Import FMapPositive.
Require Import String.
Open Scope string_scope.

Require Import domains.
Require Import kstyle.
Require Import evaluator.

Coercion EVar : string >-> Exp.
Coercion ECon : Z >-> Exp.

Lemma heap_test : forall p env,
  steps (KCfg (kra (HAssign "x" (EPlus (ELoad "x") 1%Z)) nil)
              (env :* "x" |-> p) (p |-> 12%Z) mapEmpty)
        (KCfg nil (env :* "x" |-> p) (p |-> 13%Z) mapEmpty).
Proof.
intros.
repeat (refine (more _ (@kequiv_refl _) _ _);[econstructor(reflexivity||find_map_entry)|]).
finish.
Qed.

Definition listrev :=
  (SWhile (BNot (BEq 0%Z "p"))
     (Seq (SAssign "next" (ELoad (EPlus "p" 1%Z)))
     (Seq (HAssign (EPlus "p" 1%Z) "q")
     (Seq (SAssign "q" "p")
          (SAssign "p" "next"))))).

Fixpoint listrep (l : list Z) (p : Z) (m : Map Z Z) : Prop :=
  match l with
    | nil => p = 0%Z /\ m ~= mapEmpty
    | (v :: l') =>
       p <> 0%Z /\
       exists next m',
         m ~= p |-> v :* (p + 1)%Z |-> next :* m'
         /\ listrep l' next m'
  end.

Ltac same_eprefix H :=
  match goal with
      [ H : exists _ : ?A , _ |- exists _ : ?A , _ ] =>
      let x := fresh "x" in destruct H as [x H]; exists x
  end.
  
Lemma listrep_equiv : forall l p m m', m ~= m' -> listrep l p m -> listrep l p m'.
destruct l;simpl; intuition.
rewrite <- H; assumption.
repeat same_eprefix H2.
intuition.
rewrite <- H; assumption.
Qed.

Lemma rev_test : forall lenv,
  steps (KCfg (kra listrev nil)
              ("p" |-> 1 :* "q" |-> 0 :* "next" |-> 1)%Z
              (1 |-> 12 :* 2 |-> 3 :*
               3 |-> 13 :* 4 |-> 5 :*
               5 |-> 14 :* 6 |-> 0)%Z
              lenv)
        (KCfg nil
              ("p" |-> 0 :* "q" |-> 5 :* "next" |-> 0)%Z
              (1 |-> 12 :* 2 |-> 0 :*
               3 |-> 13 :* 4 |-> 1 :*
               5 |-> 14 :* 6 |-> 3)%Z
              lenv).
Proof.
intros;repeat step_rule;finish.
Qed.

(* For a generic statement about reverse, we would like
   to have an existential about the address the reversed
   list starts at, need a different sort of reaching
   to let us put the existential where we like. *)

CoInductive reaches (s : kcfg) (phi : kcfg -> Prop) : Prop :=
 | r_done : phi s -> reaches s phi
 | r_more : forall s', kstep s s' -> reaches s' phi -> reaches s phi.

Lemma rev_pf : forall p l q l' heap0 heap_l heap_l' lenv,
  listrep l p heap_l ->
  listrep l' q heap_l' ->
  heap0 ~= heap_l :* heap_l' ->
  reaches (KCfg (kra listrev nil)
                ("p" |-> p :* "next" |-> p :* "q" |-> q)
                heap0
                lenv)
          (fun cfg' =>
             exists q' heap',
               listrep (rev_append l l') q' heap' /\
               kequiv cfg'
                      (KCfg nil
                            ("p" |-> 0 :* "next" |-> 0 :* "q" |-> q')%Z
                            heap'
                            lenv)).
Proof.
cofix.
intros.
Ltac r_step := (eapply r_more;[solve[econstructor(reflexivity||find_map_entry)]|]).
r_step.
Ltac rsplit_if :=
  cbv beta; match goal with
      | [|- reaches (KCfg (kra (KStmt (SIf (BCon ?test) _ _)) _) _ _ _) _] => split_bool test
  end.
repeat ((eapply rev_pf;fail 1) || (r_step || rsplit_if)).
(* zero case *)
clear rev_pf.
apply r_done.
exists q. exists heap0.
split;[|subst;reflexivity].
(* show l is nil *)
destruct l;destruct H;[|solve[exfalso;auto]].
simpl.
revert H0.
apply listrep_equiv.
rewrite H1, H2. equate_maps.

(* Nonzero case *)
(* Stuck on a lookup that needs domain reasoning to go through *)
(* exclude nil l*)
destruct l. (* nil *) contradict n. clear -H. destruct H. auto.
destruct H as [_ [next [m' [pequiv p_rel_l]]]].
rewrite pequiv in H1; clear pequiv.

repeat ((eapply rev_pf;fail 1) || (r_step || rsplit_if)).
simpl; eapply rev_pf.

eassumption.
split. congruence.
eexists; eexists.
split;[reflexivity|eassumption].
equate_maps.
apply equivJoin.
reflexivity.
apply equivComAssoc.
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

Lemma eval_happy : forall env,
  steps (KCfg (kra (SAssign "x" (EPlus "x" "y")) nil)
            (env :* "x" |-> 12%Z :* "y" |-> 13%Z) mapEmpty mapEmpty)
        (KCfg nil (env :* "x" |-> 25%Z :* "y" |-> 13%Z) mapEmpty mapEmpty).
intros.
repeat (refine (more _ (@kequiv_refl _) _ _);[econstructor (reflexivity || find_map_entry)|]);
simpl Zplus; finish.
Qed.

(* Try "quote" on the env *)
(* Use a mixed coinductive sequencing to use loop invariants? *)

CoFixpoint sum :
  forall (x y z : Z) erest env heap labels,
    (0 <= x)%Z ->
    z = (x + y)%Z ->
    env ~= ("i" |-> x :* "j" |-> y :* erest) ->
  steps
    (KCfg (kra (SWhile (BLe 1%Z "i")
                       (Seq
                          (SAssign "i" (EPlus "i" (-1)%Z))
                          (SAssign "j" (EPlus "j" 1%Z))))
               kdot)
                env heap labels)
    (KCfg kdot
          ("i" |-> 0%Z :* "j" |-> z%Z :* erest) heap labels).
intros; step_rule;run_circ sum.
Qed.

Lemma eval_happy' : forall env,
  steps (KCfg (kra (SAssign "x" (EPlus "x" "y")) nil)
            ("x" |-> 12%Z :* "y" |-> 13%Z :* env) mapEmpty mapEmpty)
        (KCfg nil ("x" |-> 25%Z :* "y" |-> 13%Z :* env) mapEmpty mapEmpty).
intros;
repeat (refine (more _ (@kequiv_refl _) _ _);[match goal with [|- kstep ?l _] => eapply (eval_sound l) end|]);
simpl Zplus; finish.
Qed.

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

(* Some performance tests *)
Lemma loop_test:
  steps (KCfg (kra (SWhile (BLe 0%Z "x")
    (SAssign "x" (EPlus "x" (-1)%Z)))
  nil) ("x" |-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" |-> (-1)%Z) mapEmpty mapEmpty).
Proof.
intros;
repeat (refine (more _ (@kequiv_refl _) _ _);[econstructor (reflexivity || find_map_entry)|];instantiate;simpl Zplus);
finish.
Qed.

Lemma loop_test':
  steps (KCfg (kra (SWhile (BLe 0%Z "x")
    (SAssign "x" (EPlus "x" (-1)%Z)))
  nil) ("x" |-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" |-> (-1)%Z) mapEmpty mapEmpty).
Proof.
Ltac step_eval :=refine (more _ (@kequiv_refl _) _ _);[match goal with [|- kstep ?l _] => eapply (eval_sound l) end|].
intros;repeat step_eval;simpl;finish.
Qed.

Lemma loop_test'':
  steps (KCfg (kra (SWhile (BLe (ECon 0) (EVar "x"))
    (SAssign "x" (EPlus (EVar "x") (ECon (-1)%Z))))
  nil) ("x" |-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" |-> (-1)%Z) mapEmpty mapEmpty).
Proof.
intros;apply (evals_sound 1000);lazy;repeat (apply conj);[reflexivity|simpl;equate_maps ..].
Qed.