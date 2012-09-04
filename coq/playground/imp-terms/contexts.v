Add LoadPath "../../ml_proof".

Require Import ZArith.
Require Import List.
Require Import FMapPositive.

Require Import domains.
Require Import model.

Import ImpLang.Base.
Import ImpLang.BaseM.

Set Implicit Arguments.

Generalizable Variables E env x y i b r s.

Definition add := PositiveMap.add.

Inductive step : cfg -> cfg -> Prop :=
  | s_lookup :
    `(step (plug (cfgc E env) (EVar x))
           (plug (cfgc E env) (ECon (lookup env x))))
  | s_plus : 
    `(step (plug E (EPlus (ECon x) (ECon y)))
           (plug E (ECon (x + y)%Z)))
  | s_div : `(Zneq_bool 0%Z y = true ->
    step (plug E (EDiv (ECon x) (ECon y)))
         (plug E (ECon (x / y)%Z)))
  | s_le :
    `(step (plug E (BLe (ECon x) (ECon y)))
           (plug E (BCon (Zle_bool x y))))
  | s_not :
    `(step (plug E (BNot (BCon b)))
           (plug E (BCon (negb b))))
  | s_and :
    `(step (plug E (BAnd (BCon b) r))
           (plug E (if b then r else BCon false)))
  | s_assign :
    `(step (plug (cfgc E env) (SAssign x (ECon i)))
           (plug (cfgc E (update env x i)) Skip))
  | s_seq :
    `(step (plug E (Seq Skip s))
           (plug E s))
  | s_if :
    `(step (plug E (SIf (BCon b) s1 s2))
           (plug E (if b then s1 else s2)))
  | s_while : forall E c b,
    `(step (plug E (SWhile c b))
           (plug E (SIf c (Seq b (SWhile c b)) Skip)))
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

Import TermAbbrevs.

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

(*
Definition rules : list (T * T * option T) :=
  (* lookup *)
  (plugE (cfgcE E env) (EVar x),
   plugE (cfgcE E env) (ECon (Lookup env x)),
   None) ::
  (* plus *)
  (plugE E (EPlus (ECon x) (ECon y)),
   plugE E (ECon (PlusZ x y)),
   None) ::
  (* div *)
  (plugE E (EDiv (ECon x) (ECon y)),
   plugE E (ECon (DivZ x y)),
   Some (Nez y)) ::
  (* le *)
  (plugB E (BLe (ECon x) (ECon y)),
   plugB E (BCon (Zleb x y)),
   None) ::
  (* not *)
  (plugB E (BNot (BCon b)),
   plugB E (BCon (negb b)),
   None) ::
  (* and *)
  (plugB E (BAnd (BCon (Bool true)) r),
   plugB E r,
   None) ::
  (plugB E (BAnd (BCon (Bool false)) r),
   plugB E (BCon (Bool false)),
   None) ::
  (* assign *)
  (plugS (cfgcS E env) (SAssign x (ECon i)),
   plugS (cfgcS E (Update env x i)) Skip,
   None) ::
  (* seq *)
  (plugS E (Seq Skip s),
   plugS E s,
   None) ::
  (* if *)
  (plugS E (SIf (BCon (Bool true)) s1 s2),
   plugS E s1,
   None) ::
  (plugS E (SIf (BCon (Bool false)) s1 s2),
   plugS E s2,
   None) ::
  (* while *)
  (plugS E (SWhile b s),
   plugS E (SIf b (Seq s (SWhile b s)) Skip),
   None) ::
  nil
  .
*)

Inductive Irules : (T * T * option T) -> Prop :=
  | i_lookup : Irules 
  (plugE (cfgcE E env) (EVar x),
   plugE (cfgcE E env) (ECon (Lookup env x)),
   None)
  (* plus *)
  | i_plus : Irules
  (plugE E (EPlus (ECon x) (ECon y)),
   plugE E (ECon (PlusZ x y)),
   None)
  (* div *)
  | i_div : Irules
  (plugE E (EDiv (ECon x) (ECon y)),
   plugE E (ECon (DivZ x y)),
   Some (Nez y))
  (* le *)
  | i_le : Irules
  (plugB E (BLe (ECon x) (ECon y)),
   plugB E (BCon (Zleb x y)),
   None)
  (* not *)
  | i_not : Irules
  (plugB E (BNot (BCon b)),
   plugB E (BCon (negb b)),
   None)
  (* and *)
  | i_and_t : Irules
  (plugB E (BAnd (BCon (Bool true)) r),
   plugB E r,
   None)
  | i_and_f : Irules
  (plugB E (BAnd (BCon (Bool false)) r),
   plugB E (BCon (Bool false)),
   None)  
  (* assign *)
  | i_assign : Irules
  (plugS (cfgcS E env) (SAssign x (ECon i)),
   plugS (cfgcS E (Update env x i)) Skip,
   None)
  (* seq *)
  | i_seq : Irules
  (plugS E (Seq Skip s),
   plugS E s,
   None)
  (* if *)
  | i_if_t : Irules
  (plugS E (SIf (BCon (Bool true)) s1 s2),
   plugS E s1,
   None)
  | i_if_f : Irules
  (plugS E (SIf (BCon (Bool false)) s1 s2),
   plugS E s2,
   None)
  (* while *)
  | i_while : Irules
  (plugS E (SWhile b s),
   plugS E (SIf b (Seq s (SWhile b s)) Skip),
   None)
  .

Definition rule_step r gamma gamma' :=
  match r with
  | (start,finish,cond) =>
    exists env,
       value env start = Some gamma
       /\ value env finish = Some gamma'
       /\ match cond with
            | Some c => value env c
            | None => Some (existT _ sBool true)
          end
       = Some (existT _ sBool true)
  end.

Require Import matchinglreduction.

Import ImpLang.
Module Import ImpReduction := MatchLReduction ImpLang.

Import BaseF.
Import BaseS.

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

Definition ts_rule r gamma gamma' :=
  exists rho,
    Satisfies gamma rho (fst r) /\ Satisfies gamma' rho (snd r).
Definition ts_eqv : forall S gamma gamma',
  ts S gamma gamma' <-> exists r, S r /\ ts_rule r gamma gamma'.
Proof.
  intros.
  unfold ts, ts_rule.
  split; intro H; decompose record H;
    match goal with [x : Rule |- _] => exists x end; eauto.
Qed.

(* lapply top sig...
   lemma that result is either of result sort of result,
   or bust *)

Lemma rule_to_Rule_step : forall r, forall gamma gamma',
  rule_step r gamma gamma' <->
  ts_rule (rule_to_Rule r) gamma gamma'.
Proof.
  destruct r0 as [[start finish] cond].
  unfold rule_step, ts_rule, Satisfies; simpl.

  destruct cond; simpl; intros; split;
    destruct 1 as [rho]; exists rho; intuition.
  unfold M; fold (value rho t).
  rewrite H2. reflexivity.
  unfold M in H2.
  fold (value rho t) in H2.
  destruct (value rho t);[|destruct H2].
  rewrite H2. reflexivity.
Qed.

(*
Definition ImpSystem : System := fun r => In r (map rule_to_Rule rules).
*)


Definition ImpSystem : System := fun r =>
  exists t, Irules t /\ r = rule_to_Rule t.

Definition rules_step gamma gamma' :=
  exists r, Irules r /\ rule_step r gamma gamma'.

Definition emptyV : Valuation := PositiveMap.empty (sigT sort_sem).

Definition MCtx s1 s2 := existT sort_sem (sCtxt s1 s2).
Implicit Arguments MCtx [].
Definition MStore := existT sort_sem sStore.
Definition MVar := existT sort_sem sId.
Definition MVal := existT sort_sem sVal.
Definition MBool := existT sort_sem sBool.
Definition MBExp := existT sort_sem sBExp.
Definition MExp := existT sort_sem sExp.
Definition MStmt := existT sort_sem sStmt.

Import TermAbbrevs.

Lemma step_to_rule : forall c1 c2, step c1 c2 ->
  rules_step (existT _ scfg c1) (existT _ scfg c2).
unfold rule_step.
destruct 1 as [] _eqn.
Ltac give_rule R :=
  exists R;split;[constructor|].
Ltac give_env E :=
  exists E;split;[reflexivity|split];[reflexivity|simpl].
(* lookup *)
give_rule
    (plugE (cfgcE E env) (EVar x),
     plugE (cfgcE E env) (ECon (Lookup env x)),
     @None T).
give_env
    (add Ev (MCtx sExp sStmt E0)
    (add envv (MStore env0)
    (add 3 (MVar x0) emptyV))).
tauto.
(* plus *)
give_rule
  (plugE E (EPlus (ECon x) (ECon y)),
   plugE E (ECon (PlusZ x y)),
   @None T).
give_env
  (add Ev (MCtx sExp scfg E0)
  (add xv (MVal x0)
  (add yv (MVal y0) emptyV))).
reflexivity.
(* div *)
give_rule
  (plugE E (EDiv (ECon x) (ECon y)),
   plugE E (ECon (DivZ x y)),
   Some (Nez y)).
give_env
  (add Ev (MCtx sExp scfg E0)
  (add xv (MVal x0)
  (add yv (MVal y0) emptyV))).
pose (f_equal (fun x => Some (existT sort_sem sBool x)) e).
assumption.
(* le *)
give_rule
  (plugB E (BLe (ECon x) (ECon y)),
   plugB E (BCon (Zleb x y)),
   @None T).
give_env
  (add Ev (MCtx sBExp scfg E0)
  (add xv (MVal x0)
  (add yv (MVal y0) emptyV))).
tauto.
(* not *)
give_rule
  (plugB E (BNot (BCon b)),
   plugB E (BCon (negb b)),
   @None T).
give_env
  (add Ev (MCtx sBExp scfg E0)
  (add bv (MBool b0) emptyV)).
tauto.
(* and *)
destruct b0.
give_rule
  (plugB E (BAnd (BCon (Bool true)) r),
   plugB E r,
   @None T).
give_env
  (add Ev (MCtx sBExp scfg E0)
  (add rv (MBExp r0) emptyV)).
tauto.
give_rule
  (plugB E (BAnd (BCon (Bool false)) r),
   plugB E (BCon (Bool false)),
   @None T).
give_env
  (add Ev (MCtx sBExp scfg E0)
  (add rv (MBExp r0) emptyV)).
tauto.
(* assign *)
give_rule
  (plugS (cfgcS E env) (SAssign x (ECon i)),
   plugS (cfgcS E (Update env x i)) Skip,
   @None T).
give_env
  (add Ev (MCtx sStmt sStmt E0)
  (add envv (MStore env0)
  (add xv (MVar x0)
  (add iv (MVal i0) emptyV)))).
tauto.
(* seq *)
give_rule
  (plugS E (Seq Skip s),
   plugS E s,
   @None T).
give_env
  (add Ev (MCtx sStmt scfg E0)
  (add sv (MStmt s0) emptyV)).
tauto.
(* if *)
destruct b0.
give_rule
  (plugS E (SIf (BCon (Bool true)) s1 s2),
   plugS E s1,
   @None T).
give_env
  (add Ev (MCtx sStmt scfg E0)
  (add s1v (MStmt s3)
  (add s2v (MStmt s4) emptyV))).
tauto.
give_rule
  (plugS E (SIf (BCon (Bool false)) s1 s2),
   plugS E s2,
   @None T).
give_env
  (add Ev (MCtx sStmt scfg E0)
  (add s1v (MStmt s3)
  (add s2v (MStmt s4) emptyV))). 
tauto.
(* while *)
give_rule
  (plugS E (SWhile b s),
   plugS E (SIf b (Seq s (SWhile b s)) Skip),
   @None T).
give_env
  (add Ev (MCtx sStmt scfg E0)
  (add sv (MStmt b0)
  (add bv (MBExp c) emptyV))).
tauto.
Qed.

Opaque PositiveMap.find.

Definition Mstep (gamma gamma' : sigT sort_sem) :=
  match gamma, gamma' with
    | existT scfg c1, existT scfg c2 => step c1 c2
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
unfold rules_step, rule_step, value.
intros. destruct H as [r [InR H]].
destruct InR;
  destruct H as [env0 [Hbefore [Hafter Hcond]]];
    simpl in Hbefore, Hafter, Hcond.
Ltac prog x := destruct x; try discriminate;[idtac].
Ltac pvar v venv := let m := fresh "m" in
  destruct (PositiveMap.find v venv) as [m|];[destruct m as [[]]|];try discriminate;[idtac].
Ltac reduce_hyp H :=
  unfold lapply in H; simpl in H; apply some_inj in H.
Ltac finish con :=
  (repeat match goal with [ H : @eq (option (sigT ImpLabels.sort_sem)) _ _ |- _] => reduce_hyp H;try apply M_inj in H end);
    subst; apply con; assumption.
(* lookup *)
(* digging for vars... *)
pvar Ev env0.
prog s3.
prog s4.
pvar envv env0.
pvar xv env0.
finish s_lookup.

(* plus *)
pvar Ev env0.
prog s3.
prog s4.
pvar xv env0.
pvar yv env0.
finish s_plus.

(* divide *)
pvar Ev env0.
prog s3.
prog s4.
pvar xv env0.
pvar yv env0.
finish s_div.

(* le *)
pvar Ev env0.
prog s3.
prog s4.
pvar xv env0.
pvar yv env0.
finish s_le.
(* not *)
pvar Ev env0.
prog s3.
prog s4.
pvar bv env0.
finish s_not.
(* and true *)
pvar Ev env0.
prog s3.
prog s4.
pvar rv env0.
finish s_and.
(* and false *)
pvar Ev env0.
prog s3.
prog s4.
pvar rv env0.
finish s_and.
(* assign *)
pvar Ev env0.
prog s3.
prog s4.
pvar envv env0.
pvar xv env0.
pvar iv env0.
finish s_assign.
(* skip *)
pvar Ev env0.
prog s3.
prog s4.
pvar sv env0.
finish s_seq.
(* if true *)
pvar Ev env0.
prog s3.
prog s4.
pvar s1v env0.
pvar s2v env0.
finish s_if.
(* if false *)
pvar Ev env0.
prog s3.
prog s4.
pvar s1v env0.
pvar s2v env0.
finish s_if.
(* while *)
pvar Ev env0.
prog s3.
prog s4.
pvar bv env0.
pvar sv env0.
finish s_while.
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