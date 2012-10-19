Add LoadPath "../../ml_proof".

Require Import ZArith.
Require Import List.
Require Import FMapPositive.

Require Import generic.
Require Import matchinglreduction.
Require Import matchinglproofsystem.
Require Import matchinglpartialcorrectness.

Require Import domains.
Require Import model.

Import ImpLang.
Module Import ImpReduction := MatchLReduction ImpLang.
Module Import ImpProof := MatchLProofSystem ImpLang.
Module Import ImpCorrectness := MatchLPartialCorrectness ImpLang.

Import Base BaseF BaseM BaseS.

Import TermAbbrevs.

Require Import kstyle.

Set Implicit Arguments.

Open Scope k_scope.

Import TermAbbrevs.

Open Scope kt_scope.

Inductive Krules : Rule -> Prop :=
  (* lookup *)
  | r_lookup : forall x rest env, Krules
   (Pattern (KCfg (kra (KExp (EVar x)) rest) env),
    Pattern (KCfg (kra (KExp (ECon (Lookup env x))) rest) env))
  (* assign *)
  | r_assign : forall x i rest env, Krules
  (Pattern (KCfg (kra (KStmt (SAssign x (ECon i))) rest) env),
   Pattern (KCfg (kra (KStmt Skip) rest) (Update env x i)))
  (* plus *)
  | r_plus : forall i j rest env, Krules
  (Pattern (KCfg (kra (KExp (EPlus (ECon i) (ECon j))) rest) env),
   Pattern (KCfg (kra (KExp (ECon (PlusZ i j))) rest) env))
  (* div *)
  | r_div : forall i j rest env, Krules
  (And
    (Pattern (KCfg (kra (KExp (EDiv (ECon i) (ECon j))) rest) env))
    (Equals (Bool true) (Nez j)),
   Pattern (KCfg (kra (KExp (ECon (DivZ i j))) rest) env))
  (* le *)
  | r_le : forall i j rest env, Krules
  (Pattern (KCfg (kra (KBExp (BLe (ECon i) (ECon j))) rest) env),
   Pattern (KCfg (kra (KBExp (BCon (Zleb i j))) rest) env))
  (* and true *)
  | r_and_t : forall b rest env, Krules
  (Pattern (KCfg (kra (KBExp (BAnd (BCon (Bool true)) b)) rest) env),
   Pattern (KCfg (kra (KBExp b) rest) env))
  (* and false *)
  | r_and_f : forall b rest env,  Krules
  (Pattern (KCfg (kra (KBExp (BAnd (BCon (Bool false)) b)) rest) env),
   Pattern (KCfg (kra (KBExp (BCon (Bool false))) rest) env))
  | r_skip : forall rest env, Krules
  (* skip *)
  (Pattern (KCfg (kra (KStmt Skip) rest) env),
   Pattern (KCfg rest env))
  (* if true *)
  | r_if_t : forall s1 s2 rest env, Krules
  (Pattern (KCfg (kra (KStmt (SIf (BCon (Bool true)) s1 s2)) rest) env),
   Pattern (KCfg (kra (KStmt s1) rest) env))
  (* if false *)
  | r_if_f : forall s1 s2 rest env, Krules
  (Pattern (KCfg (kra (KStmt (SIf (BCon (Bool false)) s1 s2)) rest) env),
   Pattern (KCfg (kra (KStmt s2) rest) env))
  | r_while : forall b s rest env, Krules
  (Pattern (KCfg (kra (KStmt (SWhile b s)) rest) env),
   Pattern (KCfg (kra (KStmt (SIf b (Seq s (SWhile b s)) Skip)) rest) env))
  (* heating and cooling *)
  (* plus *)
  | r_heat_plus_l : forall e e2 rest env, Krules
  (And
    (Pattern (KCfg (kra (KExp (EPlus e e2)) rest) env))
    (Equals (Bool true) (negb (isEVal e))),
   Pattern (KCfg (kra (KExp e) (kra (KFreezer (□ + e2)) rest)) env))  | r_heat_plus_r : forall e e2 rest env, Krules
  (And
    (Pattern (KCfg (kra (KExp (EPlus e e2)) rest) env))
    (Equals (Bool true) (negb (isEVal e2))),
   Pattern (KCfg (kra (KExp e2) (kra (KFreezer (e + □)) rest)) env))
  | r_cool_plus_l : forall i e rest env, Krules
  (Pattern (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ + e)) rest)) env),
   Pattern (KCfg (kra (KExp (EPlus (ECon i) e)) rest) env))
  | r_cool_plus_r : forall i e rest env, Krules
  (Pattern (KCfg (kra (KExp (ECon i)) (kra (KFreezer (e + □)) rest)) env),
   Pattern (KCfg (kra (KExp (EPlus e (ECon i))) rest) env))
  (* div *)
  | r_heat_div_l : forall e e2 rest env, Krules
  (And
    (Pattern (KCfg (kra (KExp (EDiv e e2)) rest) env))
    (Equals (Bool true)(negb (isEVal e))),
   Pattern (KCfg (kra (KExp e) (kra (KFreezer (□ / e2)) rest)) env))
  | r_heat_div_r : forall e e2 rest env, Krules
  (And
    (Pattern (KCfg (kra (KExp (EDiv e e2)) rest) env))
    (Equals (Bool true) (negb (isEVal e2))),
   Pattern (KCfg (kra (KExp e2) (kra (KFreezer (e / □)) rest)) env))
  | r_cool_div_l : forall i e rest env, Krules
  (Pattern (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ / e)) rest)) env),
   Pattern (KCfg (kra (KExp (EDiv (ECon i) e)) rest) env))
  | r_cool_div_r : forall i e rest env, Krules
  (Pattern (KCfg (kra (KExp (ECon i)) (kra (KFreezer (e / □)) rest)) env),
   Pattern (KCfg (kra (KExp (EDiv e (ECon i))) rest) env))
  (* le is seqstrict *)
  | r_heat_le_l : forall e e2 rest env, Krules
  (And
    (Pattern (KCfg (kra (KBExp (BLe e e2)) rest) env))
    (Equals (Bool true) (negb (isEVal e))),
   Pattern (KCfg (kra (KExp e) (kra (KFreezer (□ <= e2)) rest)) env))
  | r_heat_le_r : forall i e2 rest env, Krules
  (And
    (Pattern (KCfg (kra (KBExp (BLe (ECon i) e2)) rest) env))
    (Equals (Bool true) (negb (isEVal e2))),
   Pattern (KCfg (kra (KExp e2) (kra (KFreezer (i <= □)) rest)) env))
  | r_cool_le_l : forall i e rest env, Krules
  (Pattern (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ <= e)) rest)) env),
   Pattern (KCfg (kra (KBExp (BLe (ECon i) e)) rest) env))
  | r_cool_le_r : forall j i rest env, Krules
  (Pattern (KCfg (kra (KExp (ECon j)) (kra (KFreezer (i <= □)) rest)) env),
   Pattern (KCfg (kra (KBExp (BLe (ECon i) (ECon j))) rest) env))
  (* and only left-strict *)
  | r_heat_and : forall b1 b2 rest env, Krules
  (And
    (Pattern (KCfg (kra (KBExp (BAnd b1 b2)) rest) env))
    (Equals (Bool true) (negb (isBool b1))),
   Pattern (KCfg (kra (KBExp b1) (kra (KFreezer (□ && b2)) rest)) env))
  | r_cool_and : forall b b2 rest env, Krules
  (Pattern (KCfg (kra (KBExp (BCon b)) (kra (KFreezer (□ && b2)) rest)) env),
   Pattern (KCfg (kra (KBExp (BAnd (BCon b) b2)) rest) env))
  (* assign *)
  | r_heat_assign : forall x e rest env, Krules
  (And
    (Pattern (KCfg (kra (KStmt (SAssign x e)) rest) env))
    (Equals (Bool true) (negb (isEVal e))),
   Pattern (KCfg (kra (KExp e) (kra (KFreezer (x :=□)) rest)) env))
  | r_cool_assign : forall i x rest env, Krules
  (Pattern (KCfg (kra (KExp (ECon i)) (kra (KFreezer (x :=□)) rest)) env),
   Pattern (KCfg (kra (KStmt (SAssign x (ECon i))) rest) env))
  (* if *)
  | r_heat_if : forall b s1 s2 rest env, Krules
  (And
    (Pattern (KCfg (kra (KStmt (SIf b s1 s2)) rest) env))
    (Equals (Bool true) (negb (isBool b))),
   Pattern (KCfg (kra (KBExp b) (kra (KFreezer (if□then s1 else s2)) rest)) env))
  | r_cool_if : forall b s1 s2 rest env, Krules
  (Pattern (KCfg (kra (KBExp (BCon b)) (kra (KFreezer (if□then s1 else s2)) rest)) env),
   Pattern (KCfg (kra (KStmt (SIf (BCon b) s1 s2)) rest) env))
  (* seq *)
  | r_heat_seq : forall s1 s2 rest env, Krules
  (Pattern (KCfg (kra (KStmt (Seq s1 s2)) rest) env),
   Pattern (KCfg (kra (KStmt s1) (kra (KStmt s2) rest)) env))
  .

Local Open Scope positive_scope.
Definition Ev := 1.
Definition envv := 2.
Definition xv := 3.
Definition yv := 4.
Definition bv := 5.
Definition rv := 6.
Definition iv := 7.
Definition jv := 8.
Definition sv := 9.
Definition s1v := 10.
Definition s2v := 11.
Definition env'v := 12.

Definition E := TMVar Ev.
Definition env := TMVar envv.
Definition x := TMVar xv.
Definition y := TMVar yv.
Definition b := TMVar bv.
Definition r := TMVar rv.
Definition i := TMVar iv.
Definition j := TMVar jv.
Definition s := TMVar sv.
Definition s1 := TMVar s1v.
Definition s2 := TMVar s2v.
Definition env' := TMVar env'v.

Definition pvi : T := Id (domains.var 1).
Definition pvj : T := Id (domains.var 2).


(* Plan: add sort predicates like IsVar, etc,
  prove lemmas relating them to environment structure -
  and use the add x (find x m) m == m to put results in
  nice form. Then validity is nice and simple.
  *)

Definition hasSort s (result : option M) :=
  match result with
    | Some gamma => s = projT1 gamma
    | None => False
  end.

Fixpoint haveSorts ss rs {struct ss} :=
  match ss, rs with
    | nil, nil => True
    | s :: ss', res :: rs' => hasSort s res /\ haveSorts ss' rs'
    | _, _ => False
  end.

Lemma vinit' gamma s args vals op :
  Some gamma = opapply s args vals op ->
  hasSort s (opapply s args vals op).
Proof.
  revert vals; induction args; destruct vals; simpl;[congruence..|].
  destruct o as [[xs xv]|];
  [destruct (ImpLabels.sort_dec a xs);[destruct e|]|];
  [auto|congruence..].
Qed.

Lemma vinit gamma l args :
  Some gamma = lapply l args ->
    hasSort (projT1 (projT2 (label_sem l))) (lapply l args).
Proof.
  unfold lapply, ImpLabels.label_sem.
  destruct (label_sem l) as [arg [res op]].
  apply vinit'.
Qed.

Lemma vbreak s args vals op :
  hasSort s (opapply s args vals op) ->
  haveSorts args vals.
Proof.
  revert vals; induction args; destruct vals; simpl; trivial.
  destruct o as [[vs vv]|].
  destruct (ImpLabels.sort_dec a vs).
  destruct e.
  simpl. specialize (IHargs (op vv) vals). intuition.
  destruct 1.
  destruct 1.
Qed.

Lemma valid_refl : forall f,
  Valid (Implies f f).
Proof.
  unfold Valid, Satisfies. simpl. trivial.
Qed.

Lemma valid_add : forall f g,
  (Valid (Implies f g)) ->
  Valid (Implies f (And f g)).
Proof.
  unfold Valid, Satisfies. simpl. intuition.
Qed.

Lemma alf (Sys : System) pre cond post:
  Sys (And pre cond,post) ->
  forall psi, patternless psi ->
  Valid (Implies (And pre psi) cond) ->
  forall strict,
  PS strict Sys (And pre psi) (And post psi).
Proof.
  intros.
  apply ps_conseq
    with (phi1':=And (And pre cond) psi)(phi2':=(And post psi)).
  revert H1. unfold Valid, Satisfies. simpl. intuition.

  apply ps_lf. apply ps_axiom. auto.

  assumption.

  apply valid_refl.
Qed.
Implicit Arguments alf [Sys pre cond post psi strict].

Lemma conseq_l : forall phi1 phi1',
  Valid (Implies phi1 phi1') ->
  forall phi2 Sys strict,
  PS strict Sys phi1' phi2 -> PS strict Sys phi1 phi2.
Proof.
  intros. eauto using ps_conseq, valid_refl.
Qed.

(* Tactics for execution *)
Ltac valid_dec := subst;unfold Valid, Satisfies; intros; simpl; intuition.
Hint Unfold cons_System.
Hint Extern 5 (Valid _) => valid_dec.
Hint Extern 3 (patternless _) => (simpl;tauto).

Ltac unabbrev :=
  repeat match goal with
    [ T : Term positive , teq : ?T = _ |- _] =>
    rewrite teq
  end.
Ltac reabbrev :=
  repeat match goal with
    [ T : Term positive , teq : ?T = _ |- _] =>
    rewrite <- teq
  end.

Ltac step :=
eapply ps_trans;[solve[eauto 20 using ps_axiom,ps_lf,alf,Krules]|].

Ltac run := unabbrev;repeat step;instantiate;reabbrev.

(*
Lemma use_has
match PositiveMap.find envv rho with
       | Some gamma => sStore = projT1 gamma
       | None => False
       end
 *)


Lemma domain_reasoning_1
  (loopTest : Term positive)
  (HeqloopTest : loopTest = BLe (ECon (Val 1)) (EVar pvi))
  (loopBody : Term positive)
  (HeqloopBody : loopBody =
                Seq (SAssign pvi (EPlus (EVar pvi) (ECon (Val (-1)))))
                  (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1))))) :
   Valid
     (Implies
(And
           (And
              (Pattern
                 (KCfg
                    (kra
                       (KStmt
                          (SIf
                             (BCon
                                (Zleb (Val 1)
                                   (Lookup (Update (Update env pvi x) pvj y)
                                      pvi)))
                             (Seq loopBody (SWhile loopTest loopBody)) Skip))
                       kdot) (Update (Update env pvi x) pvj y)))
              (And (And (HasSort sVal x) (HasSort sVal y))
                 (HasSort sStore env))) (Equals (Bool true) (Zleb (Val 0) x)))

        
        (Or
           (And
              (And
                 (Pattern
                    (KCfg
                       (kra
                          (KStmt
                             (SIf (BCon (Bool true))
                                (Seq loopBody (SWhile loopTest loopBody))
                                Skip)) kdot)
                       (Update (Update env pvi x) pvj y)))
                 (And (And (HasSort sVal x) (HasSort sVal y))
                    (HasSort sStore env)))
              (Equals (Bool true) (Zleb (Val 0) (PlusZ x (Val (-1))))))
           (Pattern
              (KCfg
                 (kra
                    (KStmt
                       (SIf (BCon (Bool false))
                          (Seq loopBody (SWhile loopTest loopBody)) Skip))
                    kdot) (Update (Update env pvi (Val 0)) pvj (PlusZ x y)))))).

Opaque PositiveMap.find.
Opaque PositiveMap.add.
subst;unfold Valid, Satisfies; intros; simpl; intuition.
repeat
(match goal with
  | [H : exists v, PositiveMap.find _ _ = Some (existT _ _ _)
    |- _] => let v := fresh v in let Hlookup := fresh Hlookup in
             destruct H as [v Hlookup];rewrite Hlookup in * |- *
  end).
cbv [lapply ImpLabels.label_sem label_sem label projT1 projT2 eq_rec eq_rect] in H.
simpl in * |- *.

rewrite PositiveMap.gso in H by discriminate.
rewrite PositiveMap.gss in H.
remember (Zle_bool 1 v0) as bresult in H.
pose proof (Zle_cases 1%Z v0) as Hle.
rewrite <- Heqbresult in Hle.
destruct bresult;[left|right].

(* need to continue, just show tidying *)
unfold lapply;simpl;intuition.
eauto.
eauto.
eauto.

clear -Hle.
repeat apply f_equal.
symmetry.
apply Zle_imp_le_bool.
omega.

(* preparing to stop *)
Lemma some_inj (A : Set) (x y : A) :
  Some x = Some y -> x = y.
Proof.
  injection 1; trivial.
Qed.
assert (v0 = 0%Z).
clear -H1 Hle.
unfold lapply in H1; simpl in H1.

Lemma M_inj (s : Sort) (x y : sort_sem s) :
  existT _ s x = existT _ s y -> x = y.
Proof.
  apply Eqdep_dec.inj_pair2_eq_dec; exact sort_dec.
Qed.
apply M_inj in H1.
symmetry in H1.
apply Zle_bool_imp_le in H1.
omega.
subst.
assumption.
(* adjustement done *)

Qed.

Lemma domain_reasoning_2 : forall
  (loopTest : Term positive)
  (HeqloopTest : loopTest = BLe (ECon (Val 1)) (EVar pvi))
  (loopBody : Term positive)
  (HeqloopBody : loopBody =
                Seq (SAssign pvi (EPlus (EVar pvi) (ECon (Val (-1)))))
                  (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1))))),
   Valid
     (Implies
        (And
           (And
              (Pattern
                 (KCfg (kra (KStmt (SWhile loopTest loopBody)) kdot)
                    (Update
                       (Update (Update (Update env pvi x) pvj y) pvi
                          (PlusZ
                             (Lookup (Update (Update env pvi x) pvj y) pvi)
                             (Val (-1)))) pvj
                       (PlusZ
                          (Lookup
                             (Update (Update (Update env pvi x) pvj y) pvi
                                (PlusZ
                                   (Lookup (Update (Update env pvi x) pvj y)
                                      pvi) (Val (-1)))) pvj) 
                          (Val 1)))))
              (And (And (HasSort sVal x) (HasSort sVal y))
                 (HasSort sStore env)))
           (Equals (Bool true) (Zleb (Val 0) (PlusZ x (Val (-1))))))
        (ApplyF
           (PositiveMap.add xv (PlusZ x (Val (-1)))
              (PositiveMap.add yv (PlusZ y (Val 1))
                 (PositiveMap.empty (Term positive))))
           (And
              (And
                 (Pattern
                    (KCfg (kra (KStmt (SWhile loopTest loopBody)) kdot)
                       (Update (Update env pvi x) pvj y)))
                 (And (And (HasSort sVal x) (HasSort sVal y))
                    (HasSort sStore env)))
              (Equals (Bool true) (Zleb (Val 0) x))))).
Proof.
intros; subst.
simpl.
valid_dec.
unfold ImpLang.app_var in * |- *.
repeat ((rewrite PositiveMap.gso in * |- * by discriminate)
  || rewrite PositiveMap.gss in * |- *
  || rewrite PositiveMap.gempty in * |- *).
simpl in * |- *.
repeat
(match goal with
  | [H : exists v, PositiveMap.find _ _ = Some (existT _ _ _)
    |- _] => let v := fresh v in let Hlookup := fresh Hlookup in
             destruct H as [v Hlookup];rewrite Hlookup in * |- *
  end).

unfold lapply in H;simpl in H.
apply some_inj in H.
subst gamma.
unfold lapply;simpl.
apply f_equal.
apply f_equal.
apply f_equal.
repeat ((rewrite PositiveMap.gso by discriminate) || rewrite PositiveMap.gss || rewrite PositiveMap.gempty).
Transparent PositiveMap.add.
destruct v1;[|destruct v1_1];reflexivity.
Opaque PositiveMap.add.

destruct H2. exists (x0 - 1)%Z.
unfold inTerm, value', Apply', ImpLang.app_var;simpl.
repeat ((rewrite PositiveMap.gso by discriminate) || rewrite PositiveMap.gss || rewrite PositiveMap.gempty).
simpl. rewrite H0. reflexivity.

destruct H4. exists (x0 + 1)%Z.
unfold inTerm, value', Apply', ImpLang.app_var;simpl.
repeat ((rewrite PositiveMap.gso by discriminate) || rewrite PositiveMap.gss || rewrite PositiveMap.gempty).
simpl. rewrite H0. reflexivity.
Qed.

Lemma domain_reasoning_3 : forall
  (loopTest : Term positive)
  (HeqloopTest : loopTest = BLe (ECon (Val 1)) (EVar pvi))
  (loopBody : Term positive)
  (HeqloopBody : loopBody =
                Seq (SAssign pvi (EPlus (EVar pvi) (ECon (Val (-1)))))
                  (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1))))),
   Valid
     (Implies
        (ApplyF
           (PositiveMap.add xv (PlusZ x (Val (-1)))
              (PositiveMap.add yv (PlusZ y (Val 1))
                 (PositiveMap.empty (Term positive))))
           (Pattern
              (KCfg kdot (Update (Update env pvi (Val 0)) pvj (PlusZ x y)))))
        (Pattern
           (KCfg kdot (Update (Update env pvi (Val 0)) pvj (PlusZ x y))))).

intros.
simpl.
unfold Apply', ImpLang.app_var.
simpl.
repeat ((rewrite PositiveMap.gso by discriminate) || rewrite PositiveMap.gss || rewrite PositiveMap.gempty).
valid_dec.

destruct (PositiveMap.find envv rho) as [[[]]|];try discriminate H.
destruct (PositiveMap.find xv rho) as [[[]]|];try discriminate H.
destruct (PositiveMap.find yv rho) as [[[]]|];try discriminate H.

unfold lapply in * |- *; simpl in * |- *.
apply some_inj in H. subst.
replace (s3 + -1 + (s4 + 1))%Z with (s3 + s4)%Z.
reflexivity.
ring.
Qed.

Lemma sum : PS true Krules
  (And 
    (Pattern (KCfg
      (kra
        (KStmt
          (SWhile (BLe (ECon (Val 1%Z)) (EVar pvi))
            (Seq
              (SAssign pvi (EPlus (EVar pvi) (ECon (Val (-1)%Z))))
              (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1%Z)))))))
        kdot)
    (Update (Update env pvi x) pvj y)))
  (Equals (Bool true) (Zleb (Val 0%Z) x)))
  (Pattern (KCfg kdot
    (Update (Update env pvi (Val 0%Z))
      pvj (PlusZ x y)))).
Proof.

remember (BLe (ECon (Val 1)) (EVar pvi)) as loopTest.
remember (Seq (SAssign pvi (EPlus (EVar pvi) (ECon (Val (-1)))))
              (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1)))))
  as loopBody.

apply conseq_l with
  (phi1' :=
    (And
      (And (Pattern
        (KCfg (kra (KStmt (SWhile loopTest loopBody)) kdot)
          (Update (Update env pvi x) pvj y)))
      (And (And (HasSort sVal x) (HasSort sVal y)) (HasSort sStore env)))
      (Equals (Bool true) (Zleb (Val 0) x)))).

subst; unfold Valid, Satisfies; intros.
Opaque PositiveMap.find.
Opaque PositiveMap.add.
simpl. intros.
cbv [lapply ImpLabels.label_sem label_sem label projT1 projT2 eq_rec eq_rect] in H.
destruct H.
destruct (PositiveMap.find xv rho) as [[[]]|];try (discriminate H0);
destruct (PositiveMap.find envv rho) as [[[]]|];try (discriminate H);
destruct (PositiveMap.find yv rho) as [[[]]|];try (discriminate H);
simpl in H.
intuition eauto.
(* That took a while, but now we have know sorts of variables *)

eapply ps_circ.

run; auto using ps_refl.

eapply conseq_l.
eauto using domain_reasoning_1.

apply ps_case.

let n := 19 in
unabbrev;do n step;instantiate;reabbrev.

(* ready to use the circular assumption, but will
   need to subst to expand x/y *)

eapply ps_conseq.
Focus 2.
eapply ps_subst.
apply ps_axiom; left; reflexivity.
instantiate (1:=
  PositiveMap.add xv (PlusZ x (Val (-1)%Z))
  (PositiveMap.add yv (PlusZ y (Val 1%Z))
    (PositiveMap.empty _))).

eauto using domain_reasoning_2.
eauto using domain_reasoning_3.

run; auto using ps_refl.
Qed.