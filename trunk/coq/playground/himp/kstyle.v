Add LoadPath "../../ml_proof".

Require Import ZArith.
Require Import List.
Require Import FMapPositive.
Require Import String.
Open Scope string_scope.

Require Import domains.

(*
Notation "'□' '+' e" := (Fplusl e) (at level 50) : k_scope.
Notation "e '+' '□'" := (Fplusr e) (at level 50) : k_scope.
 *)
Notation FreezeL f e := (KFreezeE (fun x => f x e)).
Notation FreezeR f e := (KFreezeE (fun x => f e x)).

Notation "'□' '+' e" := (FreezeL EPlus e) (at level 50) : k_scope.
Notation "e '+' '□'" := (FreezeR EPlus e) (at level 50) : k_scope.
Notation "'□' '-' e" := (FreezeL EMinus e) (at level 50) : k_scope.
Notation "e '-' '□'" := (FreezeR EMinus e) (at level 50) : k_scope.
Notation "'□/' e" := (FreezeL EDiv e) (at level 50): k_scope.
Notation "e '/□'" := (FreezeR EDiv e) (at level 50): k_scope.
Notation "'□' '<=' e" := (FreezeL BLe e) (at level 70): k_scope.
Notation "i '<=' '□'" := (FreezeR BLe (ECon i)) (at level 70): k_scope.
Notation "'□' '&&' e" := (KFreezeB (fun l => BAnd l e)) (at level 50): k_scope.
Notation "v ':=□'" := (KFreezeE (fun e => SAssign v e)) (at level 70): k_scope.
Notation "'if□then' s1 'else' s2" := (Fif s1 s2) (at level 20): k_scope.

Delimit Scope k_scope with K.
Open Scope k_scope.

Coercion KExp : Exp >-> kitem.
Coercion KBExp : BExp >-> kitem.
Coercion KStmt : Stmt >-> kitem.
Coercion KFreezer : freezer >-> kitem.

Set Implicit Arguments.

Notation exp_step step a b :=
  (forall env henv lenv, step (KCfg a env henv lenv) (KCfg b env henv lenv)) (only parsing).

Notation exp1_step step a b := (forall rest, exp_step step (kra a rest) (kra b rest)) (only parsing).

Notation heat_step step cool hot ctx :=
  (forall rest, exp_step step (kra cool rest) (kra hot (kra ctx rest))).
Notation cool_step step hot ctx cool :=
  (forall rest, exp_step step (kra hot (kra ctx rest)) (kra cool rest)).

Generalizable Variables rest env erest henv lenv x y i j v r e b s.
Inductive kstep : kcfg -> kcfg -> Prop :=
  (* evaluation rules *)
  | k_lookup : `(env ~= (x :-> i :* erest) ->
                 kstep (KCfg (kra (EVar x) rest) env henv lenv)
                       (KCfg (kra (ECon i) rest) (x :-> i :* erest) henv lenv))
  | k_assign : `(env ~= (x :-> v :* erest) ->
                 kstep (KCfg (kra (SAssign x (ECon i)) rest) env henv lenv)
                       (KCfg (kra Skip rest) (x :-> i :* erest) henv lenv))
  | k_jump : `(forall l,
                 lenv ~= (l :-> s :* erest) ->
                 kstep (KCfg (kra (Jump l) rest) env henv lenv)
                       (KCfg (kra s kdot) env henv lenv))
  | k_plus : `(exp1_step kstep (EPlus (ECon i) (ECon j))
                               (ECon (Zplus i j)))
  | k_minus : `(exp1_step kstep (EMinus (ECon i) (ECon j))
                                (ECon (Zminus i j)))
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
  | k_cool_e : `(cool_step kstep (ECon i) (KFreezeE e) (e (ECon i)))
  (* plus *)
  | k_heat_plus_l : `(isEVal e = false ->  heat_step kstep (EPlus e e2) e  (□ + e2))
  | k_heat_plus_r : `(isEVal e2 = false -> heat_step kstep (EPlus e e2) e2 (e + □))
(*
  | k_cool_plus_l : `(cool_step kstep (ECon i) (□ + e) (EPlus (ECon i) e))
  | k_cool_plus_r : `(cool_step kstep (ECon i) (e + □) (EPlus e (ECon i)))
 *)
  (* minus *)
  | k_heat_minus_l : `(isEVal e = false ->  heat_step kstep (EMinus e e2) e  (□ - e2))
  | k_heat_minus_r : `(isEVal e2 = false -> heat_step kstep (EMinus e e2) e2 (e - □))
(*
  | k_cool_minus_l : `(cool_step kstep (ECon i) (□ - e) (EMinus (ECon i) e))
  | k_cool_minus_r : `(cool_step kstep (ECon i) (e - □) (EMinus e (ECon i)))
*)
  (* div *)
  | k_heat_div_l : `(isEVal e = false ->  heat_step kstep (EDiv e e2) e (□/ e2))
  | k_heat_div_r : `(isEVal e2 = false -> heat_step kstep (EDiv e e2) e2 (e /□))
(*
  | k_cool_div_l : `(cool_step kstep (ECon i) (□/ e) (EDiv (ECon i) e))
  | k_cool_div_r : `(cool_step kstep (ECon i) (e /□) (EDiv e (ECon i)))
 *)
  (* le is seqstrict *)
  | k_heat_le_l : `(isEVal e = false ->  heat_step kstep (BLe e e2) e (□ <= e2))
  | k_heat_le_r : `(isEVal e2 = false -> heat_step kstep (BLe (ECon i) e2) e2 (i <= □))
(*
  | k_cool_le_l : `(cool_step kstep (ECon i) (□ <= e) (BLe (ECon i) e))
  | k_cool_le_r : `(cool_step kstep (ECon j) (i <= □) (BLe (ECon i) (ECon j)))
 *)
  (* and is only strict in left argument *)
  | k_heat_and : `(isBool b1 = false -> heat_step kstep (BAnd b1 b2) b1 (□ && b2))
(*
  | k_cool_and : `(cool_step kstep (BCon b) (□ && b2) (BAnd (BCon b) b2))
 *)
  (* assign *)
  | k_heat_assign : `(isEVal e = false -> heat_step kstep (SAssign x e) e (x :=□))
(*
  | k_cool_assign : `(cool_step kstep (ECon i) (x :=□) (SAssign x (ECon i)))
 *)
  (* if *)
  | k_heat_if : `(isBool b = false -> heat_step kstep (SIf b s1 s2) b (if□then s1 else s2))
  | k_cool_if : `(cool_step kstep (BCon b) (if□then s1 else s2) (SIf (BCon b) s1 s2))
  (* seq *)
  | k_heat_seq : `(heat_step kstep (Seq s1 s2) s1 s2)
  .

Definition kequiv (k1 k2 : kcfg) : Prop :=
  match k1, k2 with
    | KCfg k1 store1 heap1 labels1,
      KCfg k2 store2 heap2 labels2 =>
      k1 = k2 /\ store1 ~= store2 /\ heap1 ~= heap2 /\ labels1 ~= labels2
  end.

CoInductive steps : kcfg -> kcfg -> Prop :=
  | done : forall c1 c2, kequiv c1 c2 -> steps c1 c2
  | more : forall c1 c2 c3, kstep c1 c2 -> steps c2 c3 -> steps c1 c3
  .

Ltac find x map k :=
  match map with
    | (x :-> _ :* _) => let pf := constr:(equivRefl map) in k pf
    | (?mapl :* (x :-> ?v)) => let pf := constr:(equivComm mapl (x :-> v)) in k pf
    | ?mapl :* ?mapr =>
           find x mapl ltac:(fun pfl => let pf := constr:(equivTrans (equivJoinL mapr pfl)
                                                                   (equivAssoc (x :-> _) _ mapr))
                                        in k pf)
        || find x mapr ltac:(fun pfr => let pf := constr:(equivTrans (equivJoinR mapl pfr)
                                                                   (mapComAssoc mapl (x :-> _) _))
                                        in k pf)
  end.
Ltac find_submap map submap k :=
  match map with
    | (submap :* _) => let pf := constr:(equivRefl map) in k pf
    | (?mapl :* submap) => let pf := constr:(equivComm mapl submap) in k pf
    | ?mapl :* ?mapr =>
           find_submap mapl submap

                       ltac:(fun pfl => let pf := constr:(equivTrans (equivJoinL mapr pfl)
                                                                   (equivAssoc submap _ mapr))
                                        in k pf)
        || find_submap mapr submap
                       ltac:(fun pfr => let pf := constr:(equivTrans (equivJoinR mapl pfr)
                                                                   (mapComAssoc mapl submap _))
                                        in k pf)
  end.

Ltac find_map_entry :=
  match goal with
    | [|- ?map ~= _ ] =>
      ((is_var map;
       match goal with
         | [H : ?map ~= ?mapr |- ?map ~= _] =>
           match mapr with
             | map => fail
             | _ => rewrite H
           end
       end)
        || (try (unfold map)));
      match goal with
        | [|- ?x :-> ?v ~= ?x :-> _ :* _] => rewrite (equivUnit (x :-> v)); reflexivity
        | [|- ?map ~= ?x :-> ?v :* ?map2 ] =>
          find x map ltac:(fun pf => exact pf)
      end
  end.

Lemma equivUnitL : forall {K V} (m : Map K V), MapEquiv (mapEmpty :* m) m.
intros. rewrite equivComm. apply equivUnit.
Qed.

Ltac equate_maps := rewrite ?equivAssoc, ?equivUnitL, ?equivUnit;
 repeat (rewrite ?f_equal;
         match goal with
           | [|- (?x :-> ?v1 :* _) ~= (?x :-> ?v2 :* _)] => apply equivJoin;[replace v1 with v2 by omega|]
           | [|- MapEquiv ?map (?x :-> _ :* _)] => find x map ltac:(fun pf => rewrite pf)
           | [|- MapEquiv ?map (?submap :* _)] => find_submap map submap ltac:(fun pf => rewrite pf)
           | [|- MapEquiv ?map ?map ] => reflexivity
         end).

Ltac finish :=
  apply done;repeat (apply conj);[reflexivity|simpl;equate_maps ..].

Lemma eval_happy : forall env,
  steps (KCfg (kra (SAssign "x" (EPlus (EVar "x") (EVar "y"))) nil)
            (env :* "x" :-> 12%Z :* "y" :-> 13%Z) mapEmpty mapEmpty)
        (KCfg nil (env :* "x" :-> 25%Z :* "y" :-> 13%Z) mapEmpty mapEmpty).
intros;
repeat (eapply more;[econstructor (reflexivity || find_map_entry)|]).
simpl Zplus; finish.
Qed.

Lemma loop_test:
  steps (KCfg (kra (SWhile (BLe (ECon 0) (EVar "x"))
    (SAssign "x" (EPlus (EVar "x") (ECon (-1)%Z))))
  nil) ("x" :-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" :-> (-1)%Z) mapEmpty mapEmpty).
Proof.
intros;
repeat (eapply more;[econstructor (reflexivity || find_map_entry)|];instantiate;simpl Zplus);
finish.
Qed.

Ltac step_rule := eapply more;[econstructor (reflexivity || find_map_entry)|].
Ltac split_if :=
  match goal with
      | [|- steps (KCfg (kra (KStmt (SIf (BCon (?x <=? ?y)%Z) _ _)) _) _ _ _) _] =>
        pose proof (Zle_cases x y); destruct (x <=? y)%Z
  end.

(* Either solve immediately by using the circularity,
   or bail out for manual intervention if the
   circularity matches structurally *)
Ltac use_circ circ :=
  solve[eapply circ;
  try (match goal with [|- _ ~= _] => equate_maps;reflexivity end);
  instantiate;  omega]
  || (eapply circ;fail 1).

Ltac run_circ circ := repeat (use_circ circ || (step_rule || split_if || finish)).

CoFixpoint sum :
  forall (x y z : Z) erest env heap labels,
    (0 <= x)%Z ->
    z = (x + y)%Z ->
    env ~= ("i" :-> x :* "j" :-> y :* erest) ->
  steps
    (KCfg (kra (SWhile (BLe (ECon 1%Z) (EVar "i"))
                       (Seq
                          (SAssign "i" (EPlus (EVar "i") (ECon (-1)%Z)))
                          (SAssign "j" (EPlus (EVar "j") (ECon 1%Z)))))
               kdot)
                env heap labels)
    (KCfg kdot
          ("i" :-> 0%Z :* "j" :-> z%Z :* erest) heap labels).
intros;step_rule;run_circ sum.
Qed.

Coercion EVar : string >-> Exp.

Definition gcdProg : Map string Stmt :=
  "gcd" :->
        SIf (BLe "a" "b")
          (SIf (BLe "b" "a")
               (Jump "done")
               (Seq (SAssign "b" (EMinus "b" "a"))
                    (Jump "gcd")))
          (Seq (SAssign "a" (EMinus "a" "b"))
               (Jump "gcd")).

Lemma label_eval : forall env,
  steps (KCfg (kra (Jump "gcd") kdot)
            (env :* "a" :-> 12%Z :* "b" :-> 13%Z) mapEmpty gcdProg)
        (KCfg (kra (Jump "done") kdot)
             (env :* "a" :-> 1%Z :* "b" :-> 1%Z) mapEmpty gcdProg).
intros; do 307 step_rule;simpl Zminus; finish.
Qed.
