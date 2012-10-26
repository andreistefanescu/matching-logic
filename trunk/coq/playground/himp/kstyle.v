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

CoInductive steps : kcfg -> kcfg -> Prop :=
  | done : forall c1 c2, kequiv c1 c2 -> steps c1 c2
  | more : forall c1 c2 c3, kstep c1 c2 -> steps c2 c3 -> steps c1 c3
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
intros;
repeat (eapply more;[econstructor (reflexivity || find_map_entry)|]);
simpl Zplus; finish.
Qed.

(* Try "quote" on the env *)
(* Use a mixed coinductive sequencing to use loop invariants? *)

Lemma eval_happy' : forall env,
  steps (KCfg (kra (SAssign "x" (EPlus (EVar "x") (EVar "y"))) nil)
            ("x" |-> 12%Z :* "y" |-> 13%Z :* env) mapEmpty mapEmpty)
        (KCfg nil ("x" |-> 25%Z :* "y" |-> 13%Z :* env) mapEmpty mapEmpty).
intros;
repeat (eapply more;[match goal with [|- kstep ?l _] => eapply (eval_sound l) end|]);
simpl Zplus; finish.
Qed.

Lemma loop_test':
  steps (KCfg (kra (SWhile (BLe (ECon 0) (EVar "x"))
    (SAssign "x" (EPlus (EVar "x") (ECon (-1)%Z))))
  nil) ("x" |-> 25%Z) mapEmpty mapEmpty)
  (KCfg nil ("x" |-> (-1)%Z) mapEmpty mapEmpty).
Proof.
Ltac step_eval :=eapply more;[match goal with [|- kstep ?l _] => eapply (eval_sound l) end|].
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
apply more with k.
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
            (env :* "a" |-> 12%Z :* "b" |-> 13%Z) mapEmpty gcdProg)
        (KCfg (kra (Jump "done") kdot)
             (env :* "a" |-> 1%Z :* "b" |-> 1%Z) mapEmpty gcdProg).
intros; do 307 step_rule;simpl Zminus; finish.
Qed.
