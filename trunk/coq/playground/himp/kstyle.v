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
  | k_lookup : `(env ~= (x |-> i :* erest) ->
                 kstep (KCfg (kra (EVar x) rest) env henv lenv)
                       (KCfg (kra (ECon i) rest) (x |-> i :* erest) henv lenv))
  | k_assign : `(env ~= (x |-> v :* erest) ->
                 kstep (KCfg (kra (SAssign x (ECon i)) rest) env henv lenv)
                       (KCfg (kra Skip rest) (x |-> i :* erest) henv lenv))
  | k_jump : `(forall l,
                 lenv ~= (l |-> s :* erest) ->
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
  | k_cool_b : `(cool_step kstep (BCon b) (KFreezeB e) (e (BCon b)))
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

Fixpoint str_split k {V} m : option (V * Map string V) :=
  match m with
    | mapEmpty => None
    | (k' |-> v) => if string_dec k k' then Some (v, mapEmpty) else None
    | (l :* r) =>
      match str_split k l with
        | Some (v, mapEmpty) => Some (v, r)
        | Some (v, l') => Some (v, l' :* r)
        | None =>
          match str_split k r with
            | Some (v, r') => Some (v, l :* r')
            | None => None
          end
      end
  end.

Lemma str_split_sound k {V} (v : V) m m' :
  str_split k m = Some (v, m') -> m ~= k |-> v :* m'.
Proof with try discriminate.
revert m'; induction m; simpl; intros... 
destruct (string_dec k k0) as [->|]...
injection H; intros; subst; clear H.
rewrite equivUnit; reflexivity.
destruct (str_split k m1) as [[v1 m'']|].
destruct m''; 
(injection H; intros; subst; clear H);
rewrite (IHm1 _ (eq_refl _)), ?equivUnit, ?equivAssoc; reflexivity.
destruct (str_split k m2) as [[v1 m'']|];try discriminate.
destruct m'';
(injection H; intros; subst; clear H);
rewrite (IHm2 _ (eq_refl _)), equivComAssoc, ?equivUnit; reflexivity.
Qed.

Fixpoint notFree' {K} (used : list K) {V} (m : Map K V) (cont : list K -> Prop) {struct m} : Prop :=
  match m with
    | mapEmpty => cont used
    | k' |-> _ => ~ In k' used /\ cont (k' :: used)
    | l :* r => notFree' used l (fun used' => notFree' used' r cont)
  end.
Definition defined {K V} (m : Map K V) : Prop := notFree' nil m (fun _ => True).  

(* want to show completeness on defined maps
Lemma str_split_complete : forall k {V} (v : V) m m', m ~= k |-> v :* m' ->
                                                      exists m'', str_split k m = Some (v, m')
                                                                  /\ m'' ~= m'.
 *)

Definition eval cfg : option kcfg :=
  match cfg with
    | KCfg nil env heap lenv => None
    | KCfg (item1 :: rest) env heap lenv =>
      let exp_step e' := Some (KCfg e' env heap lenv) in
      let heat_step e' f := exp_step (kra e' (kra f rest)) in
      let exp1_step e' := exp_step (e' :: rest) in
      match item1 with
        | ECon i =>
          match rest with
            | (KFreezeE f :: rest') => exp_step (f (ECon i) :: rest')
            | _ => None
          end
        | BCon b =>
          match rest with
            | (KFreezeB f :: rest') => exp_step (f (BCon b) :: rest')
            | (KFreezer (Fif s1 s2) :: rest') => exp_step (kra (SIf (BCon b) s1 s2) rest')
            | _ => None
          end
        | EVar x => 
          match str_split x env with
            | None => None
            | Some (v,env') => Some (KCfg (kra (ECon v) rest) (x |-> v :* env') heap lenv)
          end
        | SAssign x (ECon i) =>
          match str_split x env with
            | None => None
            | Some (_, env') => Some (KCfg (kra Skip rest) (x |-> i :* env') heap lenv)
          end
        | SAssign x e => heat_step e (x :=□)
        | Jump l =>
          match str_split l lenv with
            | None => None
            | Some (s, _) => Some (KCfg (kra s kdot) env heap lenv)
          end
        | EPlus (ECon i) (ECon j) => exp1_step (ECon (Zplus i j))
        | EPlus (ECon i) e2       => heat_step e2 (ECon i + □)
        | EPlus e1 e2             => heat_step e1 (□ + e2)
        | EMinus (ECon i) (ECon j) => exp1_step (ECon (Zminus i j))
        | EMinus (ECon i) e2       => heat_step e2 (ECon i - □)
        | EMinus e1 e2             => heat_step e1 (□ - e2)
        | EDiv (ECon i) (ECon j) =>
          if Zneq_bool 0%Z j then exp1_step (ECon (Zdiv i j)) else None
        | EDiv (ECon i) e2       => heat_step e2 (ECon i /□)
        | EDiv e1 e2             => heat_step e1 (□/ e2)
        | BLe (ECon i) (ECon j) => exp1_step (BCon (Zle_bool i j))
        | BLe (ECon i) e2       => heat_step e2 (i <= □)
        | BLe e1 e2             => heat_step e1 (□ <= e2)
        | BAnd (BCon b) be2 => if b then exp1_step be2 else exp1_step (BCon false)
        | BAnd be1 be2 => heat_step be1 (□ && be2)
        | Skip => exp_step rest
        | SIf (BCon b) s1 s2 => if b then exp1_step s1 else exp1_step s2
        | SIf be s1 s2 => heat_step be (if□then s1 else s2)
        | SWhile b s => exp1_step (SIf b (Seq s (SWhile b s)) Skip)
        | Seq s1 s2 => heat_step s1 s2

        | KFreezer _ => None
        | KFreezeE _ => None
        | KFreezeB _ => None
         (* unimplemented *)
        | BNot _ => None
        | HAssign _ _ => None
      end
end.

Functional Scheme eval_ind := Induction for eval Sort Prop.

Lemma eval_sound : forall cfg, match eval cfg with Some cfg' => kstep cfg cfg' | None => True end.
Proof.
intros.
functional induction (eval cfg);try econstructor(reflexivity || assumption ||
match goal with [H : str_split _ _ = _ |- _] => apply str_split_sound in H;eassumption end).
Qed.

Definition kequiv (k1 k2 : kcfg) : Prop :=
  match k1, k2 with
    | KCfg k1 store1 heap1 labels1,
      KCfg k2 store2 heap2 labels2 =>
      k1 = k2 /\ store1 ~= store2 /\ heap1 ~= heap2 /\ labels1 ~= labels2
  end.

Require Import Setoid.

Lemma kequiv_refl k : kequiv k k.
Proof.
destruct k;simpl;intuition reflexivity.
Qed.

Lemma kequiv_sym k1 k2 : kequiv k1 k2 -> kequiv k2 k1.
Proof.
destruct k1; destruct k2;simpl;intuition.
Qed.

Lemma kequiv_trans k1 k2 k3 : kequiv k1 k2 -> kequiv k2 k3 -> kequiv k1 k3.
Proof.
destruct k1; destruct k2; destruct k3; simpl; intuition (etransitivity; eassumption).
Qed.

Add Parametric Relation : kcfg kequiv
  reflexivity proved by kequiv_refl
  symmetry proved by kequiv_sym
  transitivity proved by kequiv_trans
  as kequiv_rel.

CoInductive steps : kcfg -> kcfg -> Prop :=
  | done : forall c1 c2, kequiv c1 c2 -> steps c1 c2
  | more : forall c1 c1' c2 c3, kequiv c1 c1' -> kstep c1' c2 -> steps c2 c3 -> steps c1 c3
  .

Ltac find x map k :=
  match map with
    | (x |-> _ :* _) => let pf := constr:(equivRefl map) in k pf
    | (?mapl :* (x |-> ?v)) => let pf := constr:(equivComm mapl (x |-> v)) in k pf
    | ?mapl :* ?mapr =>
           find x mapl ltac:(fun pfl => let pf := constr:(equivTrans (equivJoinL mapr pfl)
                                                                   (equivAssoc (x |-> _) _ mapr))
                                        in k pf)
        || find x mapr ltac:(fun pfr => let pf := constr:(equivTrans (equivJoinR mapl pfr)
                                                                   (equivComAssoc mapl (x |-> _) _))
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
                                                                   (equivComAssoc mapl submap _))
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
        | [|- ?x |-> ?v ~= ?x |-> _ :* _] => rewrite (equivUnit (x |-> v)); reflexivity
        | [|- ?map ~= ?x |-> ?v :* ?map2 ] =>
          find x map ltac:(fun pf => exact pf)
      end
  end.

Ltac equate_maps := rewrite ?equivAssoc, ?equivUnitL, ?equivUnit;
 repeat (rewrite ?f_equal;
         match goal with
           | [|- (?x |-> ?v1 :* _) ~= (?x |-> ?v2 :* _)] => apply equivJoin;[replace v1 with v2 by omega|]
           | [|- MapEquiv ?map (?x |-> _ :* _)] => find x map ltac:(fun pf => rewrite pf)
           | [|- MapEquiv ?map (?submap :* _)] => find_submap map submap ltac:(fun pf => rewrite pf)
           | [|- MapEquiv ?map ?map ] => reflexivity
         end).

Ltac finish :=
  apply done;repeat (apply conj);[reflexivity|simpl;equate_maps ..].

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

Ltac step_rule := refine (more _ (@kequiv_refl _) _ _);[econstructor (reflexivity || find_map_entry)|].
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

Lemma steps_equiv : forall s1 s2 s1' s2',
                      kequiv s1 s1' -> kequiv s2 s2' -> steps s1 s2 -> steps s1' s2'.
Proof.
cofix; intros; destruct H1.
* apply done. rewrite H, H0 in H1. assumption.
* eapply more; eauto. rewrite <- H. assumption.
  apply steps_equiv with c2 c3. reflexivity. assumption. assumption.
Qed.

Lemma steps_append : forall s1 s2 s3, steps s1 s2 -> steps s2 s3 -> steps s1 s3.
Proof.
cofix.
intros. destruct H.
* eapply steps_equiv;[symmetry;eassumption|reflexivity|eassumption].
* eapply more; eauto.
Qed.

(* A type that makes transitivity guarded *)
Inductive itsteps (ctsteps : kcfg -> kcfg -> Prop) (c1 c2 : kcfg) : Prop :=
| itstep : forall cmid, kstep c1 cmid -> ctsteps cmid c2-> itsteps ctsteps c1 c2
| ittrans : forall cmid, itsteps ctsteps c1 cmid -> ctsteps cmid c2 -> itsteps ctsteps c1 c2
.
CoInductive tsteps (c1 c2 : kcfg) : Prop :=
  | Done : c1 = c2 -> tsteps c1 c2
  | Delay : itsteps tsteps c1 c2 -> tsteps c1 c2.
Inductive PStar {A} (R : A -> A -> Prop) : A -> A -> Prop :=
  | snil : forall x, PStar R x x
  | scons : forall x y z, R x y -> PStar R y z -> PStar R x z
  .
Fixpoint ps_append {A : Type} {R : A -> A -> Prop} {c1 c2 c3 : A} (l : PStar R c1 c2)
    : PStar R c2 c3 -> PStar R c1 c3 :=
  match l with
    | snil _ => fun r => r
    | scons _ _ _ s rest => fun r => scons _ s (ps_append rest r)
  end.
Inductive it_nf (c1 c2 : kcfg): Prop :=
  | it_nf_step : forall {cmid}, kstep c1 cmid -> PStar tsteps cmid c2 -> it_nf c1 c2
  .
Fixpoint it_whnf {c1 c2} (i : itsteps tsteps c1 c2) : it_nf c1 c2 :=
  match i with
    | itstep _ s r => it_nf_step s (scons _ r (snil _ _))
    | ittrans _ l r =>
      match it_whnf l with
        | it_nf_step _ s l' => it_nf_step s (ps_append l' (scons _ r (snil _ _)))
      end
  end.
Inductive star_ts_nf (c1 c2 : kcfg) : Prop :=
  | st_nf_done : c1 = c2 -> star_ts_nf c1 c2
  | st_nf_step : forall {cmid}, kstep c1 cmid -> PStar tsteps cmid c2 -> star_ts_nf c1 c2
  .
Fixpoint star_nf {c1 c2} (l : PStar tsteps c1 c2) : star_ts_nf c1 c2 :=
  match l with
    | snil _ => st_nf_done (eq_refl _)
    | scons x y z c l' =>
      match c with
        | Done eqxy =>
          match eq_sym eqxy in _ = x return star_ts_nf x z with
            | eq_refl => star_nf l'
          end
        | Delay i =>
          match it_whnf i with
            | it_nf_step _ s l1 => st_nf_step s (ps_append l1 l')
          end
      end
  end.
CoFixpoint steps_sound {c1 c2} (l : PStar tsteps c1 c2) : steps c1 c2 :=
  match star_nf l with
    | st_nf_done eql =>
      eq_ind _ (steps c1) (done _ _ (kequiv_refl _)) _ eql
    | st_nf_step _ s l' => more _ (kequiv_refl _) s
                                (steps_sound l')
  end.
Definition tsteps_sound {c1 c2} (l : tsteps c1 c2) : steps c1 c2 :=
  steps_sound (scons _ l (snil _ _ )).

CoFixpoint mult :
  forall (x y z k t : Z) erest env heap labels,
    (0 <= x)%Z ->
    (0 <= y)%Z ->
    z = (x * y + k)%Z ->
    env ~= ("i" |-> x :* "j" |-> y :* "k" |-> k :* "t" |-> t :* erest) ->
  tsteps
    (KCfg (kra (SWhile (BLe (ECon 1%Z) (EVar "i"))
                       (Seq (SAssign "t" (EVar "j"))
                       (Seq (SAssign "i" (EPlus (EVar "i") (ECon (-1)%Z)))
                            (SWhile (BLe (ECon 1%Z) (EVar "t"))
                                    (Seq (SAssign "k" (EPlus (EVar "k") (ECon 1%Z)))
                                         (SAssign "t" (EPlus (EVar "t") (ECon (-1)%Z))))))))
               (kra (SAssign "t" (ECon 0%Z))
                    kdot))
                env heap labels)
    (KCfg kdot
          ("i" |-> 0%Z :* "j" |-> y%Z :* "k" |-> z :* "t" |-> 0%Z :* erest) heap labels)
with mult_sum :
  forall (x y z : Z) krest erest env heap labels,
    (0 <= y)%Z ->
    z = (x + y)%Z ->
    env ~= ("k" |-> x :* "t" |-> y :* erest) ->
  tsteps
    (KCfg (kra
             (SWhile (BLe (ECon 1%Z) (EVar "t"))
                     (Seq (SAssign "k" (EPlus (EVar "k") (ECon 1%Z)))
                          (SAssign "t" (EPlus (EVar "t") (ECon (-1)%Z)))))
             krest)
          env heap labels)
    (KCfg krest
          ("k" |-> z :* "t" |-> 0%Z :* erest) heap labels).
Ltac tstep := refine (Delay (itstep _ _ _ _));[econstructor (solve[reflexivity || find_map_entry])|].
Ltac tsplit_if :=
  match goal with
      | [|- tsteps (KCfg (kra (KStmt (SIf (BCon (?x <=? ?y)%Z) _ _)) _) _ _ _) _] =>
        pose proof (Zle_cases x y); destruct (x <=? y)%Z
  end.
Proof.
(* Outer *)
* intros;repeat tstep. tsplit_if.
(* harder true case *)
+
simpl in H1; subst z.
do 16 tstep.
eapply Delay. eapply ittrans.
  - eapply itstep;[solve[constructor]|].
    eapply mult_sum; clear mult mult_sum.
      Focus 3.
      instantiate (3:=k).
      instantiate (2:=y).
      instantiate (1:="j" |-> y :* "i" |-> (x + -1)%Z :* erest).
      equate_maps.
      assumption.
      simpl. reflexivity.
  - eapply mult; clear mult mult_sum.
    Focus 4.
    instantiate (3:=(x + -1)%Z).
    instantiate (2:=(k + y)%Z).
    instantiate (1:=0%Z).
    equate_maps.
    omega.
    omega.
    ring.

(* easy false case *)
+ clear mult mult_sum.
  repeat tstep.
  apply Done.
  replace x with 0%Z in * |- * by omega.
  match goal with [|- ?l = ?r] => assert (kequiv l r) end.
    solve[repeat split;try solve[equate_maps]].
    admit.

(* Inner *)
* clear mult.
  intros.
  repeat tstep. tsplit_if.
  -
  do 19 tstep.
  eapply mult_sum; clear mult_sum; try solve[equate_maps]; omega.
  - clear mult_sum.
  repeat tstep.
  apply Done.
  replace y with 0%Z by omega.
  replace x with z by omega.
  (* now they are equivalent, but ksteps was currently
     defined in terms of eq rather than kequiv.
    So, assert kequiv to prove we can, and then admit the eq *)
  match goal with [|- ?l = ?r] => assert (kequiv l r) end.
  + solve[repeat split;try solve[equate_maps]].
  + admit.
Qed.