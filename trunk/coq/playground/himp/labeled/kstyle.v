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

Notation "[ x ; .. ; y ]" := (@cons Ast x .. (@cons Ast y (@nil Ast)) ..) (at level 0).

Notation FreezeL l e := (KFreezer (fun x => AApp l [x ; e])).
Notation FreezeR l e := (KFreezer (fun x => AApp l [e ; x])).

Notation "'□' '+' e" := (FreezeL EPlus e) (at level 50) : k_scope.
Notation "e '+' '□'" := (FreezeR EPlus e) (at level 50) : k_scope.
Notation "'□' '-' e" := (FreezeL EMinus e) (at level 50) : k_scope.
Notation "e '-' '□'" := (FreezeR EMinus e) (at level 50) : k_scope.
Notation "'□/' e" := (FreezeL EDiv e) (at level 50): k_scope.
Notation "e '/□'" := (FreezeR EDiv e) (at level 50): k_scope.
Notation "'□' '<=' e" := (FreezeL BLe e) (at level 70): k_scope.
Notation "i '<=' '□'" := (FreezeR BLe i) (at level 70): k_scope.
Notation "'□' '&&' e" := (FreezeL BAnd e) (at level 50): k_scope.
Notation "v ':=□'" := (FreezeR SAssign v) (at level 70): k_scope.
Notation "'if□then' s1 'else' s2" := (KFreezer (fun b => AApp SIf (b :: s1 :: s2 :: nil))) (at level 20): k_scope.

Delimit Scope k_scope with K.
Open Scope k_scope.

Coercion AApp : label >-> Funclass.
Coercion AId : string >-> Ast.
Coercion ABool : bool >-> Ast.
Coercion AInt : Z >-> Ast.
Coercion KAst : Ast >-> kitem.

Set Implicit Arguments.

Notation exp_step step a b :=
  (forall env henv lenv, step (KCfg a env henv lenv) (KCfg b env henv lenv)) (only parsing).

Notation exp1_step step a b := (forall rest, exp_step step (kra a rest) (kra b rest)) (only parsing).

Notation heat_step step cool hot ctx :=
  (forall rest, exp_step step (kra cool rest) (kra hot (kra ctx rest))).
Notation cool_step step hot ctx cool :=
  (forall rest, exp_step step (kra hot (kra ctx rest)) (kra cool rest)).

Generalizable Variables l f rest env erest henv lenv x y i j v r e es b s.
Inductive kstep : kcfg -> kcfg -> Prop :=
  (* evaluation rules *)
  | k_lookup : `(env ~= (x |-> i :* erest) ->
                 kstep (KCfg (kra (x : string) rest) env henv lenv)
                       (KCfg (kra (i : Z) rest) (x |-> i :* erest) henv lenv))
  | k_assign : `(env ~= (x |-> v :* erest) ->
                 kstep (KCfg (kra (SAssign [x : string ; i : Z]) rest) env henv lenv)
                       (KCfg (kra (Skip nil) rest) (x |-> i :* erest) henv lenv))
  | k_jump : `(forall (l : string),
                 lenv ~= (l |-> s :* erest) ->
                 kstep (KCfg (kra (Jump [l]) rest) env henv lenv)
                       (KCfg (kra s kdot) env henv lenv))
  | k_eval_hook_zzz : `(hook l = Some (Z_Z_Z f) ->
                        exp1_step kstep (AApp l [i : Z ; j : Z])
                                        (f i j))
  | k_eval_hook_zzb : `(hook l = Some (Z_Z_bool f) ->
                        exp1_step kstep (AApp l [i : Z ; j : Z])
                                        (f i j))
  | k_eval_hook_bb : `(hook l = Some (bool_bool f) ->
                        exp1_step kstep (AApp l [b : bool])
                                        (f b))
  | k_div : `(Zneq_bool 0%Z j = true ->
               exp1_step kstep (EDiv [i : Z ; j : Z])
                               (Zdiv i j))
  | k_and_t : `(exp1_step kstep (BAnd [true ; b])
                                b)
  | k_and_f : `(exp1_step kstep (BAnd [false ; b])
                                false)
  | k_skip: `(exp_step kstep (kra (Skip nil) rest)
                             rest)
  | k_if_t : `(exp1_step kstep (SIf [true ; s1 ; s2])
                               s1)
  | k_if_f : `(exp1_step kstep (SIf [false ; s1 ; s2])
                         s2)
  | k_while : `(exp1_step kstep (SWhile [b ;  s])
                                (SIf [b ; Seq [s ; SWhile [b ; s]] ; Skip nil]))
  | k_seq : `(heat_step kstep (Seq [s1; s2]) s1 s2)
  (* heating and cooling by label *)
  | k_cool_e : `(cool_step kstep (i : Z) (KFreezer e) (e i))
  | k_cool_b : `(cool_step kstep (b : bool) (KFreezer e) (e b))
  | k_heat_1 : `(isVal e = false -> is_strict1 l = true ->
                 heat_step kstep (AApp l (e :: es)) e (KFreezer (fun e' => AApp l (e' :: es))))
  | k_heat_2 : `(orb (negb (is_sequential l))
                     (orb (negb (is_strict1 l)) (isVal e)) = true -> 
                 isVal e2 = false -> is_strict2 l = true ->
                 heat_step kstep (AApp l (e :: e2 :: es)) e2 (KFreezer (fun e2' => AApp l (e :: e2' :: es))))
  (* seq *)
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
(*
Definition eval cfg : option kcfg :=
  match cfg with
    | KCfg nil env heap lenv => None
    | KCfg (item1 :: rest) env heap lenv =>
      let exp_step e' := Some (KCfg e' env heap lenv) in
      let heat_step e' f := exp_step (kra e' (kra f rest)) in
      let exp1_step e' := exp_step (e' :: rest) in
      match item1 with
        | AInt i =>
          match rest with
            | (KFreezer f :: rest') => exp_step (f (AInt i) :: rest')
            | _ => None
          end
        | ABool b =>
          match rest with
            | (KFreezer f :: rest') => exp_step (f (ABool b) :: rest')
            | _ => None
          end
        | AId x => 
          match str_split x env with
            | None => None
            | Some (v,env') => Some (KCfg (kra v rest) (x |-> v :* env') heap lenv)
          end
        | AApp SAssign (AId x :: AInt i :: nil) =>
          match str_split x env with
            | None => None
            | Some (_, env') => Some (KCfg (kra (Skip nil) rest) (x |-> i :* env') heap lenv)
          end
        | AApp SAssign (x  :: e :: nil) => heat_step e (x :=□)
        | AApp Jump (AId l :: nil) =>
          match str_split l lenv with
            | None => None
            | Some (s, _) => Some (KCfg (kra s kdot) env heap lenv)
          end
        | AApp EPlus (AInt i :: AInt j :: nil) => exp1_step (Zplus i j)
        | AApp EPlus (AInt i :: e2 :: nil)     => heat_step e2 (i + □)
        | AApp EPlus (e1 :: e2 :: nil)         => heat_step e1 (□ + e2)
        | AApp EMinus (AInt i :: AInt j :: nil) => exp1_step (Zminus i j)
        | AApp EMinus (AInt i :: e2 :: nil)     => heat_step e2 (i - □)
        | AApp EMinus (e1 :: e2 :: nil)         => heat_step e1 (□ - e2)
        | AApp EDiv (AInt i :: AInt j :: nil) =>
          if Zneq_bool 0%Z j then exp1_step (Zdiv i j) else None
        | AApp EDiv (AInt i :: e2 :: nil)       => heat_step e2 (i /□)
        | AApp EDiv (e1 :: e2 :: nil)           => heat_step e1 (□/ e2)
        | AApp BLe (AInt i :: AInt j :: nil) => exp1_step (Zle_bool i j)
        | AApp BLe (AInt i :: e2 :: nil)     => heat_step e2 (i <= □)
        | AApp BLe (e1 :: e2 :: nil)         => heat_step e1 (□ <= e2)
        | AApp BAnd (ABool b :: be2 :: nil) => if b then exp1_step be2 else exp1_step false
        | AApp BAnd (be1 :: be2 :: nil) => heat_step be1 (□ && be2)
        | AApp Skip nil => exp_step rest
        | AApp SIf (ABool b :: s1 :: s2 :: nil) => if b then exp1_step s1 else exp1_step s2
        | AApp SIf (be :: s1 :: s2 :: nil) => heat_step be (if□then s1 else s2)
        | AApp SWhile (b :: s :: nil) => exp1_step (SIf [b; Seq [s; SWhile [b; s]]; Skip nil])
        | AApp Seq (s1 :: s2 :: nil)=> heat_step s1 s2

        | _ => None
         (* unimplemented *)
      end
end.

(*
(* Way slower in labled form! Perhaps completeness is easier? *)
Functional Scheme eval_ind := Induction for eval Sort Prop.

Lemma eval_sound : forall cfg, match eval cfg with Some cfg' => kstep cfg cfg' | None => True end.
Proof.
intros.
functional induction (eval cfg);try econstructor(reflexivity || assumption ||
match goal with [H : str_split _ _ = _ |- _] => apply str_split_sound in H;eassumption end).
Qed.
*)

Axiom str_split_complete : forall V h (x : string) (v : V) h', h ~= x |-> v :* h' -> str_split x h = Some (v, h').

Lemma eval_complete : forall cfg cfg', kstep cfg cfg' -> eval cfg <> None.
destruct 1; simpl; try discriminate;
try (match goal with [H : _ ~= _|-_] => apply str_split_complete in H;rewrite H end);
try match goal with [H : ?l = _ |- context [?l]] => rewrite H end;
try discriminate;
try solve[match goal with [H : isVal ?e = false |- _] => destruct e;discriminate end].
destruct e; try discriminate; destruct e2; discriminate.
destruct e; try discriminate; destruct e2; discriminate.
destruct e; try discriminate; destruct e2; discriminate.
destruct x; try discriminate; destruct e; discriminate.
Qed.

*)

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

Ltac step_rule := eapply more;[econstructor (reflexivity || find_map_entry)|].

Lemma eval_happy : forall env,
  steps (KCfg (kra (SAssign ["x" ; EPlus [ "x" ; "y" ]]) nil)
            (env :* "x" |-> 12%Z :* "y" |-> 13%Z) mapEmpty mapEmpty)
        (KCfg nil (env :* "x" |-> 25%Z :* "y" |-> 13%Z) mapEmpty mapEmpty).
intros; repeat step_rule; finish.
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
