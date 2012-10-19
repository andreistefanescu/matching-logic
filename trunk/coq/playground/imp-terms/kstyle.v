Add LoadPath "../../ml_proof".

Require Import ZArith.
Require Import List.
Require Import FMapPositive.

Require Import generic.

Require Import domains.
Require Import model.
Import ImpLang.Base.
Import ImpLang.BaseM.

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

Generalizable Variables rest env x y i j r e b s.

Inductive kstep : kcfg -> kcfg -> Prop :=
  (* evaluation rules *)
  | k_lookup : `(kstep (KCfg (kra (EVar x) rest) env)
                       (KCfg (kra (ECon (lookup env x)) rest) env))
  | k_assign : `(kstep (KCfg (kra (SAssign x (ECon i)) rest) env)
                       (KCfg (kra Skip rest) (update env x i)))
  | k_plus : `(kstep (KCfg (kra (EPlus (ECon i) (ECon j)) rest) env)
                     (KCfg (kra (ECon (Zplus i j)) rest) env))
  | k_div : `(Zneq_bool 0%Z j = true ->
              kstep (KCfg (kra (EDiv (ECon i) (ECon j)) rest) env)
                    (KCfg (kra (ECon (Zdiv i j)) rest) env))
  | k_le : `(kstep (KCfg (kra (BLe (ECon i) (ECon j)) rest) env)
                   (KCfg (kra (BCon (Zle_bool i j)) rest) env))
  | k_and_t : `(kstep (KCfg (kra (BAnd (BCon true) b) rest) env)
                      (KCfg (kra b rest) env))
  | k_and_f : `(kstep (KCfg (kra (BAnd (BCon false) b) rest) env)
                      (KCfg (kra (BCon false) rest) env))
  | k_skip: `(kstep (KCfg (kra Skip rest) env)
                    (KCfg rest env))
  | k_if_t : `(kstep (KCfg (kra (SIf (BCon true) s1 s2) rest) env)
                     (KCfg (kra s1 rest) env))
  | k_if_f : `(kstep (KCfg (kra (SIf (BCon false) s1 s2) rest) env)
                     (KCfg (kra s2 rest) env))
  | k_while : `(kstep (KCfg (kra (SWhile b s) rest) env)
                      (KCfg (kra (SIf b (Seq s (SWhile b s)) Skip) rest) env))
  (* heating and cooling *)
  (* plus *)
  | k_heat_plus_l : `(isEVal e = false ->
                kstep (KCfg (kra (EPlus e e2) rest) env)
                      (KCfg (kra e (kra (□ + e2) rest)) env))
  | k_heat_plus_r : `(isEVal e2 = false ->
                kstep (KCfg (kra (EPlus e e2) rest) env)
                      (KCfg (kra e2 (kra (e + □) rest)) env))
  | k_cool_plus_l : `(kstep (KCfg (kra (ECon i) (kra (□ + e) rest)) env)
                            (KCfg (kra (EPlus (ECon i) e) rest) env))
  | k_cool_plus_r : `(kstep (KCfg (kra (ECon i) (kra (e + □) rest)) env)
                            (KCfg (kra (EPlus e (ECon i)) rest) env))
  (* div *)
  | k_heat_div_l : `(isEVal e = false ->
                kstep (KCfg (kra (EDiv e e2) rest) env)
                      (KCfg (kra e (kra (□ / e2) rest)) env))
  | k_heat_div_r : `(isEVal e2 = false ->
                kstep (KCfg (kra (EDiv e e2) rest) env)
                      (KCfg (kra e2 (kra (e / □) rest)) env))
  | k_cool_div_l : `(kstep (KCfg (kra (ECon i) (kra (□ / e) rest)) env)
                           (KCfg (kra (EDiv (ECon i) e) rest) env))
  | k_cool_div_r : `(kstep (KCfg (kra (ECon i) (kra (e / □) rest)) env)
                           (KCfg (kra (EDiv e (ECon i)) rest) env))
  (* le is seqstrict *)
  | k_heat_le_l : `(isEVal e = false ->
                kstep (KCfg (kra (BLe e e2) rest) env)
                      (KCfg (kra e (kra (□ <= e2) rest)) env))
  | k_heat_le_r : `(isEVal e2 = false ->
                kstep (KCfg (kra (BLe (ECon i) e2) rest) env)
                      (KCfg (kra e2 (kra (i <= □) rest)) env))
  | k_cool_le_l : `(kstep (KCfg (kra (ECon i) (kra (□ <= e) rest)) env)
                            (KCfg (kra (BLe (ECon i) e) rest) env))
  | k_cool_le_r : `(kstep (KCfg (kra (ECon j) (kra (i <= □) rest)) env)
                            (KCfg (kra (BLe (ECon i) (ECon j)) rest) env))
  (* and only left-strict *)
  | k_heat_and : `(isBool b1 = false ->
                 kstep (KCfg (kra (BAnd b1 b2) rest) env)
                       (KCfg (kra b1 (kra (□ && b2) rest)) env))
  | k_cool_and : `(kstep (KCfg (kra (BCon b) (kra (□ && b2) rest)) env)
                         (KCfg (kra (BAnd (BCon b) b2) rest) env))
  (* assign *)
  | k_heat_assign : `(isEVal e = false ->
                  kstep (KCfg (kra (SAssign x e) rest) env)
                        (KCfg (kra e (kra (x :=□) rest)) env))
  | k_cool_assign : `(kstep (KCfg (kra (ECon i) (kra (x :=□) rest)) env)
                            (KCfg (kra (SAssign x (ECon i)) rest) env))

  (* if *)
  | k_heat_if : `(isBool b = false ->
               kstep (KCfg (kra (SIf b s1 s2) rest) env)
                     (KCfg (kra b (kra (if□then s1 else s2) rest)) env))
  | k_cool_if : `(
               kstep (KCfg (kra (BCon b) (kra (if□then s1 else s2) rest)) env)
                     (KCfg (kra (SIf (BCon b) s1 s2) rest) env))
  (* seq *)
  | k_heat_seq : `(kstep (KCfg (kra (Seq s1 s2) rest) env)
                         (KCfg (kra s1 (kra s2 rest)) env))
  .

Inductive steps : kcfg -> kcfg -> Prop :=
  | done : forall c, steps c c
  | more : forall c1 c2 c3, kstep c1 c2 -> steps c2 c3 -> steps c1 c3
  .

Lemma eval_happy :
  steps (KCfg (kra (SAssign (var 1) (EPlus (EVar (var 1)) (EVar (var 2)))) nil)
            (update (update (PositiveMap.empty _) (var 1) 12%Z) (var 2) 13%Z))
        (KCfg nil (update (update (PositiveMap.empty _) (var 1) 25%Z) (var 2) 13%Z)).

Proof.
repeat (eapply more;[solve[auto using kstep]|cbv]).
apply done.
Qed.

Lemma loop_test:
  steps (KCfg (kra (SWhile (BLe (ECon 0) (EVar (var 1)))
    (SAssign (var 1) (EPlus (EVar (var 1)) (ECon (-1)%Z))))
  nil) (update (PositiveMap.empty _) (var 1) 25%Z))
  (KCfg nil (update (PositiveMap.empty _) (var 1) (-1)%Z)).
Proof.
repeat (eapply more;[solve[auto using kstep]|cbv]).
apply done.
Qed.

Import TermAbbrevs.
Notation "'□' '+' e" := (Fplusl e) (at level 50) : kt_scope.
Notation "e '+' '□'" := (Fplusr e) (at level 50) : kt_scope.
Notation "'□' '/' e" := (Fdivl e) (at level 40): kt_scope.
Notation "e '/' '□'" := (Fdivr e) (at level 40): kt_scope.
Notation "'□' '<=' e" := (Flel e) (at level 70): kt_scope.
Notation "i '<=' '□'" := (Fler i) (at level 70): kt_scope.
Notation "'□' '&&' e" := (Fandl e) (at level 40): kt_scope.
Notation "v ':=□'" := (Fassign v) (at level 30): kt_scope.
Notation "'if□then' s1 'else' s2" := (Fif s1 s2) (at level 20): kt_scope.

Delimit Scope kt_scope with KT.
Open Scope kt_scope.

(*
Local Open Scope positive_scope.
Definition restv := 1.
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
Definition ev := 13.
Definition e2v := 14.
Definition b1v := 15.
Definition b2v := 16.

Definition rest := TMVar restv.
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
Definition e := TMVar ev.
Definition e2 := TMVar e2v.
Definition b1 := TMVar b1v.
Definition b2 := TMVar b2v.

(* With unsorted terms, kitem injections can't be
   coercions. Maybe labels should be refined
   to make kra do the injection itself?
   would require partial operations in the labels *)

Definition rules : list (T * T * option T) :=
  (* lookup *)
  (KCfg (kra (KExp (EVar x)) rest) env,
   KCfg (kra (KExp (ECon (Lookup env x))) rest) env,
   None) ::
  (* assign *)
  (KCfg (kra (KStmt (SAssign x (ECon i))) rest) env,
   KCfg (kra (KStmt Skip) rest) (Update env x i),
   None) ::
  (* plus *)
  (KCfg (kra (KExp (EPlus (ECon i) (ECon j))) rest) env,
   KCfg (kra (KExp (ECon (PlusZ i j))) rest) env,
   None) ::
  (* div *)
  (KCfg (kra (KExp (EDiv (ECon i) (ECon j))) rest) env,
   KCfg (kra (KExp (ECon (DivZ i j))) rest) env,
   Some (Nez j)) ::
  (* le *)
  (KCfg (kra (KBExp (BLe (ECon i) (ECon j))) rest) env,
   KCfg (kra (KBExp (BCon (Zleb i j))) rest) env,
   None) ::
  (* and true *)
  (KCfg (kra (KBExp (BAnd (BCon (Bool true)) b)) rest) env,
   KCfg (kra (KBExp b) rest) env,
   None) ::
  (* and false *)
  (KCfg (kra (KBExp (BAnd (BCon (Bool false)) b)) rest) env,
   KCfg (kra (KBExp (BCon (Bool false))) rest) env,
   None) ::
  (* skip *)
  (KCfg (kra (KStmt Skip) rest) env,
   KCfg rest env,
   None) ::
  (* if true *)
  (KCfg (kra (KStmt (SIf (BCon (Bool true)) s1 s2)) rest) env,
   KCfg (kra (KStmt s1) rest) env,
   None) ::
  (* if false *)
  (KCfg (kra (KStmt (SIf (BCon (Bool false)) s1 s2)) rest) env,
   KCfg (kra (KStmt s2) rest) env,
   None) ::
  (KCfg (kra (KStmt (SWhile b s)) rest) env,
   KCfg (kra (KStmt (SIf b (Seq s (SWhile b s)) Skip)) rest) env,
   None) ::
  (* heating and cooling *)
  (* plus *)
  (KCfg (kra (KExp (EPlus e e2)) rest) env,
   KCfg (kra (KExp e) (kra (KFreezer (□ + e2)) rest)) env,
   Some (negb (isVal e))) ::
  (KCfg (kra (KExp (EPlus e e2)) rest) env,
   KCfg (kra (KExp e2) (kra (KFreezer (e + □)) rest)) env,
   Some (negb (isVal e2))) ::
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ + e)) rest)) env,
   KCfg (kra (KExp (EPlus (ECon i) e)) rest) env,
   None) ::
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (e + □)) rest)) env,
   KCfg (kra (KExp (EPlus e (ECon i))) rest) env,
   None) ::
  (* div *)
  (KCfg (kra (KExp (EDiv e e2)) rest) env,
   KCfg (kra (KExp e) (kra (KFreezer (□ / e2)) rest)) env,
   Some (negb (isVal e))) ::
  (KCfg (kra (KExp (EDiv e e2)) rest) env,
   KCfg (kra (KExp e2) (kra (KFreezer (e / □)) rest)) env,
   Some (negb (isVal e2))) ::
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ / e)) rest)) env,
   KCfg (kra (KExp (EDiv (ECon i) e)) rest) env,
   None) ::
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (e / □)) rest)) env,
   KCfg (kra (KExp (EDiv e (ECon i))) rest) env,
   None) ::
  (* le is seqstrict *)
  (KCfg (kra (KBExp (BLe e e2)) rest) env,
   KCfg (kra (KExp e) (kra (KFreezer (□ <= e2)) rest)) env,
   Some (negb (isVal e))) ::
  (KCfg (kra (KBExp (BLe (ECon i) e2)) rest) env,
   KCfg (kra (KExp e2) (kra (KFreezer (i <= □)) rest)) env,
   Some (negb (isVal e2))) ::
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ <= e)) rest)) env,
   KCfg (kra (KBExp (BLe (ECon i) e)) rest) env,
   None) ::
  (KCfg (kra (KExp (ECon j)) (kra (KFreezer (i <= □)) rest)) env,
   KCfg (kra (KBExp (BLe (ECon i) (ECon j))) rest) env,
   None) ::
  (* and only left-strict *)
  (KCfg (kra (KBExp (BAnd b1 b2)) rest) env,
   KCfg (kra (KBExp b1) (kra (KFreezer (□ && b2)) rest)) env,
   Some (negb (isBool b1))) ::
  (KCfg (kra (KBExp (BCon b)) (kra (KFreezer (□ && b2)) rest)) env,
   KCfg (kra (KBExp (BAnd (BCon b) b2)) rest) env,
   None) ::
  (* assign *)
  (KCfg (kra (KStmt (SAssign x e)) rest) env,
   KCfg (kra (KExp e) (kra (KFreezer (x :=□)) rest)) env,
   Some (negb (isVal e))) ::
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (x :=□)) rest)) env,
   KCfg (kra (KStmt (SAssign x (ECon i))) rest) env,
   None) ::
  (* if *)
  (KCfg (kra (KStmt (SIf b s1 s2)) rest) env,
   KCfg (kra (KBExp b) (kra (KFreezer (if□then s1 else s2)) rest)) env,
   Some (negb (isBool b))) ::
  (KCfg (kra (KBExp (BCon b)) (kra (KFreezer (if□then s1 else s2)) rest)) env,
   KCfg (kra (KStmt (SIf (BCon b) s1 s2)) rest) env,
   None) ::
  (* seq *)
  (KCfg (kra (KStmt (Seq s1 s2)) rest) env,
   KCfg (kra (KStmt s1) (kra (KStmt s2) rest)) env,
   None) ::
  nil.

Inductive Irules : (T * T * option T) -> Prop :=
  (* lookup *)
  | i_lookup : Irules
  (KCfg (kra (KExp (EVar x)) rest) env,
   KCfg (kra (KExp (ECon (Lookup env x))) rest) env,
   None)
  (* assign *)
  | i_assign : Irules
  (KCfg (kra (KStmt (SAssign x (ECon i))) rest) env,
   KCfg (kra (KStmt Skip) rest) (Update env x i),
   None)
  (* plus *)
  | i_plus : Irules
  (KCfg (kra (KExp (EPlus (ECon i) (ECon j))) rest) env,
   KCfg (kra (KExp (ECon (PlusZ i j))) rest) env,
   None)
  (* div *)
  | i_div : Irules
  (KCfg (kra (KExp (EDiv (ECon i) (ECon j))) rest) env,
   KCfg (kra (KExp (ECon (DivZ i j))) rest) env,
   Some (Nez j))
  (* le *)
  | i_le : Irules
  (KCfg (kra (KBExp (BLe (ECon i) (ECon j))) rest) env,
   KCfg (kra (KBExp (BCon (Zleb i j))) rest) env,
   None)
  (* and true *)
  | i_and_t : Irules
  (KCfg (kra (KBExp (BAnd (BCon (Bool true)) b)) rest) env,
   KCfg (kra (KBExp b) rest) env,
   None)
  | i_and_f : Irules
  (* and false *)
  (KCfg (kra (KBExp (BAnd (BCon (Bool false)) b)) rest) env,
   KCfg (kra (KBExp (BCon (Bool false))) rest) env,
   None)
  | i_skip : Irules
  (* skip *)
  (KCfg (kra (KStmt Skip) rest) env,
   KCfg rest env,
   None)
  (* if true *)
  | i_if_t : Irules
  (KCfg (kra (KStmt (SIf (BCon (Bool true)) s1 s2)) rest) env,
   KCfg (kra (KStmt s1) rest) env,
   None)
  (* if false *)
  | i_if_f : Irules
  (KCfg (kra (KStmt (SIf (BCon (Bool false)) s1 s2)) rest) env,
   KCfg (kra (KStmt s2) rest) env,
   None)
  | i_while : Irules
  (KCfg (kra (KStmt (SWhile b s)) rest) env,
   KCfg (kra (KStmt (SIf b (Seq s (SWhile b s)) Skip)) rest) env,
   None)
  (* heating and cooling *)
  (* plus *)
  | i_heat_plus_l : Irules
  (KCfg (kra (KExp (EPlus e e2)) rest) env,
   KCfg (kra (KExp e) (kra (KFreezer (□ + e2)) rest)) env,
   Some (negb (isVal e)))
  | i_heat_plus_r : Irules
  (KCfg (kra (KExp (EPlus e e2)) rest) env,
   KCfg (kra (KExp e2) (kra (KFreezer (e + □)) rest)) env,
   Some (negb (isVal e2)))
  | i_cool_plus_l : Irules
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ + e)) rest)) env,
   KCfg (kra (KExp (EPlus (ECon i) e)) rest) env,
   None)
  | i_cool_plus_r : Irules
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (e + □)) rest)) env,
   KCfg (kra (KExp (EPlus e (ECon i))) rest) env,
   None)
  (* div *)
  | i_heat_div_l : Irules
  (KCfg (kra (KExp (EDiv e e2)) rest) env,
   KCfg (kra (KExp e) (kra (KFreezer (□ / e2)) rest)) env,
   Some (negb (isVal e)))
  | i_heat_div_r : Irules
  (KCfg (kra (KExp (EDiv e e2)) rest) env,
   KCfg (kra (KExp e2) (kra (KFreezer (e / □)) rest)) env,
   Some (negb (isVal e2)))
  | i_cool_div_l : Irules
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ / e)) rest)) env,
   KCfg (kra (KExp (EDiv (ECon i) e)) rest) env,
   None)
  | i_cool_div_r : Irules
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (e / □)) rest)) env,
   KCfg (kra (KExp (EDiv e (ECon i))) rest) env,
   None)
  (* le is seqstrict *)
  | i_heat_le_l : Irules
  (KCfg (kra (KBExp (BLe e e2)) rest) env,
   KCfg (kra (KExp e) (kra (KFreezer (□ <= e2)) rest)) env,
   Some (negb (isVal e)))
  | i_heat_le_r : Irules
  (KCfg (kra (KBExp (BLe (ECon i) e2)) rest) env,
   KCfg (kra (KExp e2) (kra (KFreezer (i <= □)) rest)) env,
   Some (negb (isVal e2)))
  | i_cool_le_l : Irules
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (□ <= e)) rest)) env,
   KCfg (kra (KBExp (BLe (ECon i) e)) rest) env,
   None)
  | i_cool_le_r : Irules
  (KCfg (kra (KExp (ECon j)) (kra (KFreezer (i <= □)) rest)) env,
   KCfg (kra (KBExp (BLe (ECon i) (ECon j))) rest) env,
   None)
  (* and only left-strict *)
  | i_heat_and : Irules
  (KCfg (kra (KBExp (BAnd b1 b2)) rest) env,
   KCfg (kra (KBExp b1) (kra (KFreezer (□ && b2)) rest)) env,
   Some (negb (isBool b1)))
  | i_cool_and : Irules
  (KCfg (kra (KBExp (BCon b)) (kra (KFreezer (□ && b2)) rest)) env,
   KCfg (kra (KBExp (BAnd (BCon b) b2)) rest) env,
   None)
  (* assign *)
  | i_heat_assign : Irules
  (KCfg (kra (KStmt (SAssign x e)) rest) env,
   KCfg (kra (KExp e) (kra (KFreezer (x :=□)) rest)) env,
   Some (negb (isVal e)))
  | i_cool_assign : Irules
  (KCfg (kra (KExp (ECon i)) (kra (KFreezer (x :=□)) rest)) env,
   KCfg (kra (KStmt (SAssign x (ECon i))) rest) env,
   None)
  (* if *)
  | i_heat_if : Irules
  (KCfg (kra (KStmt (SIf b s1 s2)) rest) env,
   KCfg (kra (KBExp b) (kra (KFreezer (if□then s1 else s2)) rest)) env,
   Some (negb (isBool b)))
  | i_cool_if : Irules
  (KCfg (kra (KBExp (BCon b)) (kra (KFreezer (if□then s1 else s2)) rest)) env,
   KCfg (kra (KStmt (SIf (BCon b) s1 s2)) rest) env,
   None)
  (* seq *)
  | i_heat_seq : Irules
  (KCfg (kra (KStmt (Seq s1 s2)) rest) env,
   KCfg (kra (KStmt s1) (kra (KStmt s2) rest)) env,
   None).

Lemma Irules_rules : forall r, Irules r <-> In r rules.
Proof.
split.
destruct 1;repeat ((left;reflexivity)||right).

intro H.
repeat (destruct H as [<-|];[constructor|]).
destruct H.
Qed.

Require Import matchinglreduction.

Module Import ImpReduction := MatchLReduction ImpLang.
Import BaseF.

Definition rule_to_Rule : (T * T * option T) -> Rule := fun r =>
  match r with
    | (before, after, cond) =>
      match cond with
        | Some t =>
          (And (Pattern before)
            (Equals t (Bool true)),
            Pattern after)
        | None =>
          (Pattern before,
            Pattern after)
      end
  end.

(* equivalent to ts (map rule_to_Rule rules),
   but with the In hoisted *)
Import BaseS.

Definition rules_step gamma gamma' :=
  exists r : (T * T * option T),
    Irules r /\
    exists rho : Valuation,
      match r with
        | (first, second, cond) =>
          Some gamma = value rho first /\
          Some gamma' = value rho second /\
          match cond with
            | Some c => Some (existT _ sBool true) = value rho c
            | None => True
          end
      end.

Lemma step_to_rule : forall c1 c2, kstep c1 c2 ->
  rules_step (existT _ skcfg c1) (existT _ skcfg c2).
Ltac pattern_rule :=
match goal with
  [ H : kstep ?lhs ?rhs |- _] =>
  term_quote lhs ltac:(fun lhst =>
  term_quote rhs ltac:(fun rhst =>
    eexists (lhst,rhst,_)))
end.
Ltac find_rule :=
  split;[constructor|].

Ltac find_env :=
  unfold x, e, e2, i, j, b, b1, b2, s, s1, s2, rest, env;
    match goal with
      [|- exists _ : _,
        Some (existT _ _ ?val) = value _ ?pat /\ _ /\ _] =>
      align_rule val pat (PositiveMap.empty M) 
      ltac:(fun env' => exists env')
    end.
Ltac finish := intuition;
 (unfold value; simpl;
  unfold lapply;simpl;
  apply f_equal;apply f_equal;
    match goal with
      [H : _ = _ |- _] => rewrite H; reflexivity
    end).

unfold rules_step.
destruct 1 as [] _eqn: Heq; clear Heq;
 pattern_rule; find_rule; find_env; solve[finish].
Qed.

Opaque PositiveMap.find.

Definition Mstep (gamma gamma' : sigT sort_sem) :=
  match gamma, gamma' with
    | existT skcfg c1, existT skcfg c2 => kstep c1 c2
    | _, _ => False
  end.

Lemma some_inj (A : Set) (x y : A) :
  Some x = Some y -> x = y.
Proof.
  injection 1; trivial.
Qed.
Lemma M_inj (s : Sort) (x y : sort_sem s) :
  existT _ s x = existT _ s y -> x = y.
Proof.
  apply Eqdep_dec.inj_pair2_eq_dec; exact sort_dec.
Qed.

Lemma rule_to_step : forall gamma gamma',
  rules_step gamma gamma' -> Mstep gamma gamma'.
Ltac prog x := destruct x; try discriminate;[idtac].
Ltac pvar v venv := let m := fresh "m" in
  destruct (PositiveMap.find v venv) as [m|];[destruct m as [[]]|];try discriminate;[idtac].
Ltac reduce_hyp H :=
  unfold lapply in H; simpl in H; apply some_inj in H.
Ltac give_rule con :=
  (repeat match goal with [ H : @eq (option (sigT ImpLabels.sort_sem)) _ _ |- _] => reduce_hyp H;try apply M_inj in H end);
    subst; apply con; assumption.
Ltac give_rule':=
  (repeat match goal with [ H : @eq (option (sigT ImpLabels.sort_sem)) _ _ |- _] => reduce_hyp H;try apply M_inj in H end);
    subst; unfold Mstep; 
  match goal with
    [ H : true = Datatypes.negb _ |- _] =>
    pose (Bool.negb_sym _ _ H)
    |   _ => idtac
  end;solve[auto using kstep].

unfold rules_step, value.
intros. destruct H as [r [InR H]].
destruct InR; destruct H as [env0 [Hbefore [Hafter Hcond]]];
    simpl in Hbefore, Hafter, Hcond;
try (
repeat match goal with
 [H : context E [PositiveMap.find ?v ?e] |- _] =>
   pvar v e
  end; give_rule').
Qed.

Theorem rule_adequate : forall gamma gamma',
  Mstep gamma gamma' <-> rules_step gamma gamma'.
Proof.
split.

unfold Mstep; intro H.
destruct gamma as [[]]; try (exfalso; assumption).
destruct gamma' as [[]]; try (exfalso; assumption).
apply step_to_rule; assumption.

apply rule_to_step.
Qed.

Import TermAbbrevs.

 *)