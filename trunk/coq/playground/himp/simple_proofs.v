Require Import ZArith.
Require Import List.
Require Import FMapPositive.
Require Import String.
Open Scope string_scope.

Require Import domains.
Require Import kstyle.
Require Import coinduction.

Coercion EVar : string >-> Exp.
Coercion ECon : Z >-> Exp.

Open Scope Z_scope.

(* One thing to try is defining a simple wrapper to turn a parameterized rule
   into a relation, see if we can get it automatically *)

Ltac kequiv_tac := repeat (apply conj);[reflexivity|simpl;equate_maps ..].
Ltac kstep_tac := econstructor(reflexivity || (simpl;find_map_entry)).

(*
(* Either solve immediately by using the circularity,
   or bail out for manual intervention if the
   circularity matches structurally *)
Ltac use_circ circ :=
  solve[eapply circ;
  try (match goal with [|- _ ~= _] => equate_maps;reflexivity end);
  instantiate;  omega]
  || (eapply circ;fail 1).

Ltac run := repeat (step_rule || split_if || finish).
Ltac run_circ circ := repeat (use_circ circ || (step_rule || split_if || finish)).

Ltac tstep := refine (Delay (itstep _ _ _ _));[econstructor (solve[reflexivity || find_map_entry])|].
Ltac tsplit_if := cbv beta; (* reduce redexes left from plugging *)
  match goal with
      | [|- tsteps (KCfg (kra (KStmt (SIf (BCon (?x <=? ?y)%Z) _ _)) _) _ _ _) _] =>
        pose proof (Zle_cases x y); destruct (x <=? y)%Z
  end.
 *)

Notation basic_goal rel :=
  (forall env,
  rel (KCfg (kra (SAssign "x" (EPlus "x" "y")) nil)
            (env :* "x" |-> 12%Z :* "y" |-> 13%Z) mapEmpty mapEmpty)
      (kequiv (KCfg nil (env :* "x" |-> 25%Z :* "y" |-> 13%Z) mapEmpty mapEmpty))).
(* Very basic example, no heaps or labels, and even using derived rules *)
Lemma direct_coinduction : basic_goal reaches.
intros.
repeat (eapply step;[econstructor (reflexivity || find_map_entry)|]);apply done.
repeat split;equate_maps.
Qed.

(* Using tactics for kstep, kequiv *)
Lemma basic_tacs : basic_goal reaches.
intros.
repeat (eapply step;[kstep_tac|]);apply done;kequiv_tac.
Qed.

Ltac steps_run := repeat (eapply step;[kstep_tac|]);apply done;kequiv_tac.

(* Now using derived rules *)

(* Try to either finish immediately or take a step at a stepF goal *)
Ltac first_step := (apply DoneF;kequiv_tac) || (eapply StepF;[kstep_tac|]).
Ltac by_rules rules := let H :=
  fresh in assert (sound rules) as H;[apply trans_sound;destruct 1;first_step|intros;apply H;constructor].

Inductive basic_rule : RRel := BasicGoal : basic_goal basic_rule.

Lemma derived_rules : basic_goal reaches.
by_rules basic_rule.
repeat (eapply tstep;[kstep_tac|]);apply tdone;kequiv_tac.
Qed.

(* Make a basic run tactic *)
Ltac tstep_tac := eapply tstep;[kstep_tac|].
Ltac tfinish_tac := solve[apply tdone;kequiv_tac].

Ltac trun_basic := repeat tstep_tac;try tfinish_tac.

Lemma trun_basic_test : basic_goal reaches.
by_rules basic_rule;trun_basic.
Qed.

Notation heap_goal rel :=
  (forall p env, rel (KCfg (kra (HAssign "x" (EPlus (ELoad "x") 1%Z)) nil)
              (env :* "x" |-> p) (p |-> 12%Z) mapEmpty)
        (kequiv (KCfg nil (env :* "x" |-> p) (p |-> 13%Z) mapEmpty))).

Inductive heap_rule : RRel := HeapGoal : heap_goal heap_rule.
(* Now an example program that has a heap *)
Lemma heap_test : heap_goal reaches.
Proof.
by_rules heap_rule;trun_basic.
Qed.

(* Slightly more compilicated example, needing to split. *)
Definition step (state event : Z) :=
  match state, event with
    | Z0, Z0 => 1
    | _, _ => 0
  end.
Lemma step_ZZ : forall s e, s = 0 -> e = 0 -> step s e = 1.
intros;subst;reflexivity. Qed.
Lemma step_N1 : forall s e, s <> 0 -> step s e = 0.
intros;destruct s;simpl;congruence. Qed.
Lemma step_N2 : forall s e, e <> 0 -> step s e = 0.
intros;destruct s;destruct e;simpl;congruence. Qed.
Create HintDb step_simpl discriminated.
Hint Rewrite step_ZZ step_N1 step_N2 using assumption: step_simpl.

Notation split_goal rel := (forall state addr event,
  rel (KCfg (kra (SIf
                 (BAnd (BEq (ELoad "state") 0) (BEq "event" 0))
                 (HAssign "state" 1)
                 (HAssign "state" 0)) nil)
              ("event" |-> event :* "state" |-> addr) (addr |-> state) mapEmpty)
      (kequiv (KCfg nil
              ("event" |-> event :* "state" |-> addr) (addr |-> (step state event)) mapEmpty))).
Inductive split_rules : RRel := SplitGoal : split_goal split_rules.

(* First split manually *)
Lemma manual_split : split_goal reaches.
Proof.
by_rules split_rules;trun_basic.
(* Gets stuck at split *)
destruct state;trun_basic.
destruct event;trun_basic.
Qed. 
Close Scope Z_scope.

Ltac split_bool bexp :=
  match bexp with
    | negb ?bexp' => split_bool bexp'
    | (?x <=? ?y)%Z => destruct (Z.leb_spec x y)
    | (?x =? ?y)%Z  => destruct (Z.eqb_spec x y)
  end.
Ltac tsplit_if :=
  cbv beta; match goal with
      | [|- trans _ (KCfg (kra (KStmt (SIf (BCon ?test) _ _)) _) _ _ _) _] => split_bool test
      | [|- trans _ (KCfg (kra (KBExp (BAnd (BCon ?test) _)) _) _ _ _) _] => split_bool test
  end.

Ltac trun_split finish_simpl := repeat (tstep_tac || tsplit_if);finish_simpl;try tfinish_tac.

Lemma auto_split : split_goal reaches.
Proof.
by_rules split_rules;trun_split ltac:(autorewrite with step_simpl).
Qed. 
Close Scope Z_scope.

(* List reverse *) 
Definition listrev :=
  (SWhile (BNot (BEq 0%Z "p"))
     (Seq (SAssign "next" (ELoad (EPlus "p" 1%Z))) 
     (Seq (HAssign (EPlus "p" 1%Z) "q")
     (Seq (SAssign "q" "p")
          (SAssign "p" "next"))))).

(* Representation predicate *)
Fixpoint listrep (l : list Z) (p : Z) (m : Map Z Z) : Prop :=
  match l with
    | nil => p = 0%Z /\ m ~= mapEmpty
    | (v :: l') =>
       p <> 0%Z /\
       exists next m',
         m ~= p |-> v :* (p + 1)%Z |-> next :* m'
         /\ listrep l' next m'
  end.

(*
Ltac same_eprefix H :=
  match goal with
      [ H : exists _ : ?A , _ |- exists _ : ?A , _ ] =>
      let x := fresh "x" in destruct H as [x H]; exists x
  end.
*)

Lemma listrep_equiv : forall l p m m', m ~= m' -> listrep l p m -> listrep l p m'.
destruct l;simpl; intuition.
setoid_rewrite <- H; assumption.
Qed.

(* Test a concrete execution of list reverse *)
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
intros;steps_run.
Qed.

(* Brute force attempt to simplify all representation predicates *)
Ltac simplify_listrep := repeat
  match goal with
    | [H : listrep ?l _ ?heap |- _] =>
      let pf := fresh in
      destruct l;
        [destruct H as [pf H]
        |destruct H as [pf [? [? [H ?]]]]];
        try (exfalso;omega);[clear pf];
        try (rewrite H in * |- *;clear H heap)
  end.

(* Need to adjust tactics to stop at circularities, and maybe do something
   about automatically cleaning up lists *)

(* Idea 1: assume circularities have non-overlapping <k> in left-hand side,
   so we can commit to the first that unifies and (fail 1) if we couldn't
   satisfy it's hypotheses *)
(* Idea 2: add into the run cycle a tactic that recognizes lookups on an
   address registered with a representation predicate, and unfolds/splits to
   make progress
 *)
(* Idea 3: probably folding can be handled by writing invariant rules with
   folded conclusions, and then we only have to deal with it at the finish
   while trying to validate that rule
 *)

(*
Ltac stop_at_circ circ := (eapply circ; fail 1).
(* add to find_map_entry a thing that unfolds/splits *)
Ltac r_step := (eapply r_more;[solve[econstructor(reflexivity||find_map_entry)]|]).
(* Add a thing that cleans up *)
Ltac rsplit_if :=
  cbv beta; match goal with
      | [|- reaches (KCfg (kra (KStmt (SIf (BCon ?test) _ _)) _) _ _ _) _] => split_bool test
  end.
Ltac r_run circ := repeat (stop_at_circ circ || (r_step || (rsplit_if;simplify_listrep))).

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
intros. r_step.
r_run rev_pf.
(* zero case *)
clear rev_pf.
apply r_done.

eexists;eexists;split;[eassumption|].
simpl;rewrite H1;repeat split;(reflexivity||equate_maps).
(* nonzero case, use circularity *)
simpl; eapply rev_pf.

eassumption.
Focus 2.
(* Why does equiv_maps fail here? - rewrite equivUnit instantiates the evar*)
match goal with
  | [|- MapEquiv ?map (?submap :* _)] => find_submap map submap ltac:(fun pf => rewrite pf)
end.
reflexivity.

simpl. split;[congruence|]. eexists;eexists;split;[|eassumption]. 
equate_maps.
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
 *)