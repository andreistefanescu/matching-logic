Add LoadPath "../../ml_proof".

Require Import ZArith.
Require Import List.
Require Import FMapPositive.
Require Import String.
Open Scope string_scope.

Require Import domains.

Notation "'□' '+' e" := (Fplusl e) (at level 50) : k_scope.
Notation "e '+' '□'" := (Fplusr e) (at level 50) : k_scope.
Notation "'□' '/' e" := (Fdivl e) (at level 40): k_scope.
Notation "e '/' '□'" := (Fdivr e) (at level 40): k_scope.
Notation "'□' '<=' e" := (Flel e) (at level 70): k_scope.
Notation "i '<=' '□'" := (Fler i) (at level 70): k_scope.
Notation "'□' '&&' e" := (Fandl e) (at level 40): k_scope.
Notation "v ':=□'" := (Fassign v) (at level 30): k_scope.
Notation "'if□then' s1 'else' s2" := (Fif s1 s2) (at level 20): k_scope.

Delimit Scope k_scope with K.
Open Scope k_scope.

Coercion KExp : Exp >-> kitem.
Coercion KBExp : BExp >-> kitem.
Coercion KStmt : Stmt >-> kitem.
Coercion KFreezer : freezer >-> kitem.

Set Implicit Arguments.

Notation exp1_step step a b :=
  (forall rest env henv, step (KCfg (kra a rest) env henv) 
                              (KCfg (kra b rest) env henv)) (only parsing).
Notation exp_step step a b :=
  (forall env henv, step (KCfg a env henv) (KCfg b env henv)) (only parsing).

Generalizable Variables rest env erest henv x y i j v r e b s.
Inductive kstep : kcfg -> kcfg -> Prop :=
  (* evaluation rules *)
  | k_lookup : `(env = (x :-> i :* erest) ->
                 kstep (KCfg (kra (EVar x) rest) env henv)
                       (KCfg (kra (ECon i) rest) (x :-> i :* erest) henv))
  | k_assign : `(env = (x :-> v :* erest) ->
                 kstep (KCfg (kra (SAssign x (ECon i)) rest) env henv)
                       (KCfg (kra Skip rest) (x :-> i :* erest) henv))
  | k_plus : `(exp1_step kstep (EPlus (ECon i) (ECon j))
                               (ECon (Zplus i j)))
  | k_div : `(Zneq_bool 0%Z j = true ->
               exp1_step kstep (EDiv (ECon i) (ECon j))
                               (ECon (Zdiv i j)))
  | k_le : `(exp1_step kstep (BLe (ECon i) (ECon j))
                             (BCon (Zle_bool i j)))
  | k_and_t : `(exp1_step kstep (BAnd (BCon true) b)
                                b)
  | k_and_f : `(exp1_step kstep (BAnd (BCon false) b)
                                (BCon false))
  | k_skip: `(exp_step kstep (kra Skip rest)
                             rest)
  | k_if_t : `(exp1_step kstep (SIf (BCon true) s1 s2)
                               s1)
  | k_if_f : `(exp1_step kstep (SIf (BCon false) s1 s2)
                         s2)
  | k_while : `(exp1_step kstep (SWhile b s)
                                (SIf b (Seq s (SWhile b s)) Skip))
  (* heating and cooling *)
  (* plus *)
  | k_heat_plus_l : `(isEVal e = false ->
                exp_step kstep (kra (EPlus e e2) rest)
                               (kra e (kra (□ + e2) rest)))
  | k_heat_plus_r : `(isEVal e2 = false ->
                exp_step kstep (kra (EPlus e e2) rest)
                               (kra e2 (kra (e + □) rest)))
  | k_cool_plus_l : `(exp_step kstep (kra (ECon i) (kra (□ + e) rest))
                                     (kra (EPlus (ECon i) e) rest))
  | k_cool_plus_r : `(exp_step kstep (kra (ECon i) (kra (e + □) rest))
                                     (kra (EPlus e (ECon i)) rest))
  (* div *)
  | k_heat_div_l : `(isEVal e = false ->
                exp_step kstep (kra (EDiv e e2) rest)
                               (kra e (kra (□ / e2) rest)))
  | k_heat_div_r : `(isEVal e2 = false ->
                exp_step kstep (kra (EDiv e e2) rest)
                               (kra e2 (kra (e / □) rest)))
  | k_cool_div_l : `(exp_step kstep (kra (ECon i) (kra (□ / e) rest))
                                    (kra (EDiv (ECon i) e) rest))
  | k_cool_div_r : `(exp_step kstep (kra (ECon i) (kra (e / □) rest))
                                    (kra (EDiv e (ECon i)) rest))
  (* le is seqstrict *)
  | k_heat_le_l : `(isEVal e = false ->
                exp_step kstep (kra (BLe e e2) rest)
                               (kra e (kra (□ <= e2) rest)))
  | k_heat_le_r : `(isEVal e2 = false ->
                exp_step kstep (kra (BLe (ECon i) e2) rest)
                               (kra e2 (kra (i <= □) rest)))
  | k_cool_le_l : `(exp_step kstep (kra (ECon i) (kra (□ <= e) rest))
                                   (kra (BLe (ECon i) e) rest))
  | k_cool_le_r : `(exp_step kstep (kra (ECon j) (kra (i <= □) rest))
                                   (kra (BLe (ECon i) (ECon j)) rest))
  (* and only left-strict *)
  | k_heat_and : `(isBool b1 = false ->
                 exp_step kstep (kra (BAnd b1 b2) rest)
                                (kra b1 (kra (□ && b2) rest)))
  | k_cool_and : `(exp_step kstep (kra (BCon b) (kra (□ && b2) rest))
                                  (kra (BAnd (BCon b) b2) rest))
  (* assign *)
  | k_heat_assign : `(isEVal e = false ->
                  exp_step kstep (kra (SAssign x e) rest)
                                 (kra e (kra (x :=□) rest)))
  | k_cool_assign : `(exp_step kstep (kra (ECon i) (kra (x :=□) rest))
                                     (kra (SAssign x (ECon i)) rest))

  (* if *)
  | k_heat_if : `(isBool b = false ->
               exp_step kstep (kra (SIf b s1 s2) rest)
                              (kra b (kra (if□then s1 else s2) rest)))
  | k_cool_if : `(
               exp_step kstep (kra (BCon b) (kra (if□then s1 else s2) rest))
                              (kra (SIf (BCon b) s1 s2) rest))
  (* seq *)
  | k_heat_seq : `(exp_step kstep (kra (Seq s1 s2) rest)
                                  (kra s1 (kra s2 rest)))
  .

CoInductive steps : kcfg -> kcfg -> Prop :=
  | done : forall c1 c2, c1 = c2 -> steps c1 c2
  | more : forall c1 c2 c3, kstep c1 c2 -> steps c2 c3 -> steps c1 c3
  .

Ltac find x map k :=
  match map with
    | (x :-> _ :* _) => let pf := constr:(eq_refl map) in k pf
    | (?mapl :* (x :-> ?v)) => let pf := constr:(mapComm mapl (x :-> v)) in k pf
    | ?mapl :* ?mapr =>
           find x mapl ltac:(fun pfl => let pf := constr:(eq_trans (f_equal (fun m => m :* mapr) pfl)
                                                                   (mapAssoc (x :-> _) _ mapr))
                                        in k pf)
        || find x mapr ltac:(fun pfr => let pf := constr:(eq_trans (f_equal (fun m => mapl :* m) pfr)
                                                                   (mapComAssoc mapl (x :-> _) _))
                                        in k pf)
  end.
Ltac find_submap map submap k :=
  match map with
    | (submap :* _) => let pf := constr:(eq_refl map) in k pf
    | (?mapl :* submap) => let pf := constr:(mapComm mapl submap) in k pf
    | ?mapl :* ?mapr =>
           find_submap mapl submap
                       ltac:(fun pfl => let pf := constr:(eq_trans (f_equal (fun m => m :* mapr) pfl)
                                                                   (mapAssoc submap _ mapr))
                                        in k pf)
        || find_submap mapr submap
                       ltac:(fun pfr => let pf := constr:(eq_trans (f_equal (fun m => mapl :* m) pfr)
                                                                   (mapComAssoc mapl submap _))
                                        in k pf)
  end.

Ltac find_map_entry :=
  match goal with
    | [|- ?x :-> ?v = ?x :-> _ :* _] => rewrite <- (mapUnit (x :-> v)); reflexivity
    | [|- ?map = ?x :-> ?v :* ?map2 ] =>
      find x map ltac:(fun pf => exact pf)
  end.

Lemma mapUnitL : forall {A} (m : Map A), mapEmpty :* m = m.
intros. rewrite mapComm. apply mapUnit.
Qed.

Ltac equate_maps := rewrite ?mapAssoc, ?mapUnitL, ?mapUnit;
 repeat (rewrite ?f_equal;
         match goal with
           | [|- (?x :-> _ :* _) = (?x :-> _ :* _)] => apply f_equal2;[apply f_equal;omega|]
           | [|-?map = ?x :-> _ :* _] => find x map ltac:(fun pf => rewrite pf)
           | [|-?map = ?submap :* _] => find_submap map submap ltac:(fun pf => rewrite pf)
           | [|- ?map = ?map ] => reflexivity
         end).

Ltac finish :=
  apply done; apply (f_equal2 (KCfg _)); equate_maps.

Lemma eval_happy : forall env,
  steps (KCfg (kra (SAssign "x" (EPlus (EVar "x") (EVar "y"))) nil)
            (env :* "x" :-> 12%Z :* "y" :-> 13%Z) mapEmpty)
        (KCfg nil (env :* "x" :-> 25%Z :* "y" :-> 13%Z) mapEmpty).
intros;
repeat (eapply more;[econstructor (reflexivity || find_map_entry)|]).
simpl Zplus;finish.
Qed.

Lemma loop_test:
  steps (KCfg (kra (SWhile (BLe (ECon 0) (EVar "x"))
    (SAssign "x" (EPlus (EVar "x") (ECon (-1)%Z))))
  nil) ("x" :-> 25%Z) mapEmpty)
  (KCfg nil ("x" :-> (-1)%Z) mapEmpty).
Proof.
intros;
repeat (eapply more;[econstructor (reflexivity || find_map_entry)|];instantiate;simpl Zplus);
finish.
Qed.

Ltac step_rule := eapply more;[econstructor (reflexivity || find_map_entry)|].
Ltac split_if :=
  match goal with
      | [|- steps (KCfg (kra (KStmt (SIf (BCon (?x <=? ?y)%Z) _ _)) _) _ _) _] =>
        pose proof (Zle_cases x y); destruct (x <=? y)%Z
  end.

Ltac use_circ circ :=
  eapply circ;
  try (match goal with [|- @eq (Map string) _ _] => equate_maps;reflexivity end);
  instantiate;  omega.

Ltac run_circ circ := repeat (use_circ circ || (step_rule || split_if || finish)).

CoFixpoint sum :
  forall (x y z : Z) erest env heap,
    (0 <= x)%Z ->
    z = (x + y)%Z ->
    env = ("i" :-> x :* "j" :-> y :* erest) ->
  steps
    (KCfg (kra (SWhile (BLe (ECon 1%Z) (EVar "i"))
                       (Seq
                          (SAssign "i" (EPlus (EVar "i") (ECon (-1)%Z)))
                          (SAssign "j" (EPlus (EVar "j") (ECon 1%Z)))))
               kdot)
                env heap)
    (KCfg kdot
          ("i" :-> 0%Z :* "j" :-> z%Z :* erest) heap).
intros. subst env.
step_rule; run_circ sum.
Qed.