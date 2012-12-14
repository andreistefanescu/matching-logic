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
Notation "'□<=' e" := (FreezeL BLe e) (at level 70): k_scope.
Notation "i '<=□'" := (FreezeR BLe (ECon i)) (at level 70): k_scope.
Notation "'□==' e" := (FreezeL BEq e) (at level 70): k_scope.
Notation "i '==□'" := (FreezeR BEq (ECon i)) (at level 70): k_scope.
Notation "'□&&' e" := (KFreezeB (fun l => BAnd l e)) (at level 50): k_scope.
Notation "v ':=□'" := (KFreezeE (fun e => SAssign v e)) (at level 70): k_scope.
Notation "'if□then' s1 'else' s2" := (KFreezeB (fun b => SIf b s1 s2)) (at level 20): k_scope.

Delimit Scope k_scope with K.
Open Scope k_scope.

Coercion KExp : Exp >-> kitem.
Coercion KBExp : BExp >-> kitem.
Coercion KStmt : Stmt >-> kitem.

Set Implicit Arguments.

Notation exp_step step a b :=
  (forall env henv lenv, step (KCfg a env henv lenv) (KCfg b env henv lenv)) (only parsing).

Notation exp1_step step a b := (forall rest, exp_step step (kra a rest) (kra b rest)) (only parsing).

Notation heat_step step cool hot ctx :=
  (forall rest, exp_step step (kra cool rest) (kra hot (kra ctx rest))).
Notation cool_step step hot ctx cool :=
  (forall rest, exp_step step (kra hot (kra ctx rest)) (kra cool rest)).

Generalizable Variables rest env erest henv hrest lenv x y i j v r e b s.
Inductive kstep : kcfg -> kcfg -> Prop :=
  (* evaluation rules *)
  | k_lookup : `(env ~= (x |-> i :* erest) ->
                 kstep (KCfg (kra (EVar x) rest) env henv lenv)
                       (KCfg (kra (ECon i) rest) (x |-> i :* erest) henv lenv))
  | k_load : `(henv ~= (i |-> j :* hrest) ->
                 kstep (KCfg (kra (ELoad (ECon i)) rest) env henv lenv)
                       (KCfg (kra (ECon j) rest) env henv lenv))
  | k_assign : `(env ~= (x |-> v :* erest) ->
                 kstep (KCfg (kra (SAssign x (ECon i)) rest) env henv lenv)
                       (KCfg             rest (x |-> i :* erest) henv lenv))
  | k_hassign : `(henv ~= (i |-> v :* hrest) ->
                 kstep (KCfg (kra (HAssign (ECon i) (ECon j)) rest) env henv lenv)
                       (KCfg                     rest env (i |-> j :* hrest) lenv))
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
  | k_eq : `(exp1_step kstep (BEq (ECon i) (ECon j))
                             (BCon (i =? j)%Z))
  | k_not : `(exp1_step kstep (BNot (BCon b)) (BCon (negb b)))
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
  (* unary *)
  | k_heat_load : `(isEVal e = false -> heat_step kstep (ELoad e) e (KFreezeE ELoad))
  (* plus *)
  | k_heat_plus_l : `(isEVal e = false ->  heat_step kstep (EPlus e e2) e  (□ + e2))
  | k_heat_plus_r : `(isEVal e2 = false -> heat_step kstep (EPlus e e2) e2 (e + □))
  (* minus *)
  | k_heat_minus_l : `(isEVal e = false ->  heat_step kstep (EMinus e e2) e  (□ - e2))
  | k_heat_minus_r : `(isEVal e2 = false -> heat_step kstep (EMinus e e2) e2 (e - □))
  (* div *)
  | k_heat_div_l : `(isEVal e = false ->  heat_step kstep (EDiv e e2) e (□/ e2))
  | k_heat_div_r : `(isEVal e2 = false -> heat_step kstep (EDiv e e2) e2 (e /□))
  (* le is seqstrict *)
  | k_heat_le_l : `(isEVal e = false ->  heat_step kstep (BLe e e2) e (□<= e2))
  | k_heat_le_r : `(isEVal e2 = false -> heat_step kstep (BLe (ECon i) e2) e2 (i <=□))
  (* eq is seqstrict *)
  | k_heat_eq_l : `(isEVal e = false ->  heat_step kstep (BEq e e2) e (□== e2))
  | k_heat_eq_r : `(isEVal e2 = false -> heat_step kstep (BEq (ECon i) e2) e2 (i ==□))
  (* and is only strict in left argument *)
  | k_heat_not : `(isBool b = false -> heat_step kstep (BNot b) b (KFreezeB BNot))
  | k_heat_and : `(isBool b1 = false -> heat_step kstep (BAnd b1 b2) b1 (□&& b2))
  (* assign *)
  | k_heat_assign : `(isEVal e = false -> heat_step kstep (SAssign x e) e (x :=□))
  (* hassign *)
  | k_heat_hassign_l : `(isEVal e  = false -> heat_step kstep (HAssign e e2) e  (FreezeL HAssign e2))
  | k_heat_hassign_r : `(isEVal e2 = false -> heat_step kstep (HAssign e e2) e2 (FreezeR HAssign e))
  (* if *)
  | k_heat_if : `(isBool b = false -> heat_step kstep (SIf b s1 s2) b (if□then s1 else s2))
  (* seq *)
  | k_heat_seq : `(heat_step kstep (Seq s1 s2) s1 s2)
  .

Fixpoint notFree' {K} (used : list K) {V} (m : Map K V) (cont : list K -> Prop) {struct m} : Prop :=
  match m with
    | mapEmpty => cont used
    | k' |-> _ => ~ In k' used /\ cont (k' :: used)
    | l :* r => notFree' used l (fun used' => notFree' used' r cont)
  end.
Definition defined {K V} (m : Map K V) : Prop := notFree' nil m (fun _ => True).  

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

Lemma kstep_equiv : forall s1 s2, kstep s1 s2 ->
  forall s1', kequiv s1 s1' -> exists s2', kstep s1' s2' /\ kequiv s2 s2'.
Proof.
destruct 1;destruct s1';simpl;
intro Hequiv1;destruct Hequiv1 as (Hkcell & Hstore & Henv & Hlabels);
rewrite <- ?Hkcell, ?Hstore, ?Henv, ?Hlabels in * |- *;
refine (ex_intro _ (KCfg _ _ _ _) _);
(split;
[econstructor (eassumption || reflexivity)|]);
try solve[repeat split;(assumption || reflexivity)].
Qed.

CoInductive steps : kcfg -> kcfg -> Prop :=
  | done : forall c1 c2, kequiv c1 c2 -> steps c1 c2
  | more : forall c1 c1' c2 c3, kequiv c1 c1' -> kstep c1' c2 -> steps c2 c3 -> steps c1 c3
  .

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

Ltac finish :=
  apply done;repeat (apply conj);[reflexivity|simpl;equate_maps ..].

Ltac step_rule := refine (more _ (@kequiv_refl _) _ _);[econstructor (reflexivity || (simpl;find_map_entry))|].
Ltac split_bool bexp :=
  match bexp with
    | negb ?bexp' => split_bool bexp'
    | (?x <=? ?y)%Z => destruct (Z.leb_spec x y)
    | (?x =? ?y)%Z  => destruct (Z.eqb_spec x y)
  end.
Ltac split_if :=
  cbv beta; match goal with
      | [|- steps (KCfg (kra (KStmt (SIf (BCon ?test) _ _)) _) _ _ _) _] => split_bool test
      | [|- steps (KCfg (kra (KBExp (BAnd (BCon ?test) _)) _) _ _ _) _] => split_bool test
  end.

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
Ltac tsplit_if := cbv beta; (* reduce redexes left from plugging *)
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
do 14 tstep.
eapply Delay. eapply ittrans.
  - eapply itstep;[solve[econstructor(reflexivity||equate_maps)]|].
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
  do 17 tstep.
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