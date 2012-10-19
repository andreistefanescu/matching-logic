Add LoadPath "../../ml_proof".

Require Import List.

Require Import FMapPositive.
Require Import ZArith.

Require Import matchinglreduction.
Require Import matchinglproofsystem.
Require Import matchinglpartialcorrectness.

Require Import contexts.
Require Import model.

Import ImpLang.
Module Import ImpReduction := MatchLReduction ImpLang.
Module Import ImpProof := MatchLProofSystem ImpLang.
Module Import ImpCorrectness := MatchLPartialCorrectness ImpLang.

Import Base BaseF BaseM BaseS.

Import TermAbbrevs.

(* prepare for inversion of environments *)
Opaque PositiveMap.find.
Opaque PositiveMap.add.

Lemma rule_package : forall gamma gamma',
  rules_step gamma gamma'
  <-> ts ImpSystem gamma gamma'.
Proof.
  intros. rewrite ts_eqv. unfold rules_step, ImpSystem.

  setoid_rewrite rule_to_Rule_step.
  split; intro H; decompose [ex and] H; subst; eauto.
Qed.

Opaque ImpLabels.sort_dec.
Ltac split_var v env :=
    let x := fresh "x" in
    let val := fresh "val" in
    let e := fresh "e" in
    destruct (PositiveMap.find v env) as [[x val]|];[|discriminate];
    match goal with
      [ H : context C [ImpLabels.sort_dec ?s x] |- _] =>
      destruct (ImpLabels.sort_dec s x) as [e|];[|discriminate];destruct e
    end.
Ltac destruct_env :=
  (repeat match goal with
    [ H : context E [PositiveMap.find ?var ?env] |- _]
    => split_var var env
  end); change ImpLabels.sort_dec with sort_dec in * |- *;
  simpl in * |- *.

Theorem impproper : entails_system true (ts ImpSystem) ImpSystem.
Proof.
  apply wd_proper_refl.
  intro; intros.

  unfold ImpSystem in H.
  destruct H as [t [Hin ->]].

  destruct Hin; unfold wd_rule, Satisfies; simpl; intros;

  (unfold lapply in H |- *; simpl in H |- *;
   decompose record H; destruct_env; eexists; reflexivity).
Qed.

Definition imp_star := PS19 ImpSystem.
Definition imp_plus := PS29 ImpSystem.

Lemma ts_mstep (a b : M) : ts ImpSystem a b <-> Mstep a b.
  pose proof (rule_package a b).
  pose proof (rule_adequate a b).
  tauto.
Qed.

Theorem imp_rule_partial_correctness
  : forall phi phi' : Formula,
  PS19 ImpSystem phi phi' ->
  entails false (ts ImpSystem) (phi,phi').
Proof.
  intros phi phi'.
  apply partial_correctness.
  exact impproper.
Qed.

Theorem imp_partial_correctness : forall phi phi' : Formula,
  PS19 ImpSystem phi phi' ->
  entails false Mstep (phi,phi').
Proof.
  intros.
  apply imp_rule_partial_correctness in H.
  unfold entails; intros.
  assert (terminates gamma (ts ImpSystem)).
    clear -H0. induction H0; constructor.
      intros. apply H0. apply ts_mstep. assumption.

  destruct (H gamma H2 rho H1).
  exists x.
  intuition.
  revert H4; apply clos_weaken.
  apply ts_mstep.
Qed.

Lemma assign : entails false Mstep
  (Pattern (Cfg (SAssign x (ECon i)) env),
   Pattern (Cfg Skip (Update env x i))).
Proof.
apply imp_partial_correctness. (* start matching logic proof *)

apply ps_conseq with
  (phi1' := (Pattern (plugS (cfgcS Shole env) (SAssign x (ECon i)))))
  (phi2' := (Pattern (plugS (cfgcS Shole (Update env x i)) Skip))).
  (* weaken *)
  unfold Valid, Satisfies, Implies; simpl; unfold lapply; simpl; intros; destruct_env; trivial.
  (* validity by brute force ^^^ *)
  change (PS false ImpSystem
      (ApplyF (Base.Update identity (existT _ E I) Shole)
        (Pattern (plugS (cfgcS E env) (SAssign x (ECon i)))))
      (ApplyF (Base.Update identity (existT _ E I) Shole)
        (Pattern (plugS (cfgcS E (Update env x i)) Skip)))).
  apply ps_subst.
  apply ps_axiom. unfold ImpSystem. eauto using Irules.
  (* other validity *)
  unfold Valid, Satisfies, Implies; simpl; unfold lapply; simpl; intros; destruct_env; trivial.
Qed.

Ltac valid_tac :=  unfold Valid, Satisfies, Implies; simpl;
  unfold lapply; simpl; intros; destruct_env; trivial.

Lemma r_lookup' : forall extrules E' env' x' strict phi1 phi2,
  Valid (Implies phi1 (Pattern (plugE (cfgcE E' env') (EVar x')))) ->
  Valid (Implies (Pattern (plugE (cfgcE E' env') (ECon (Lookup env' x')))) phi2) 
  -> PS strict (List.fold_right cons_System ImpSystem extrules) phi1 phi2.
Proof.
  intros.
  refine (ps_conseq strict _ _ _ _ _ H _ H0).
  pose (subst :=
      Base.Update (Base.Update (Base.Update identity
      (existT _ E I) E')
      (existT _ env I) env')
      (existT _ x I) x').
  apply ps_conseq with
    (phi1' := (ApplyF subst
      (Pattern (plugE (cfgcE E env) (EVar x)))))
    (phi2' := (ApplyF subst
      (Pattern (plugE (cfgcE E env) (ECon (Lookup env x))))));
    clear;[valid_tac| |valid_tac].
  apply ps_subst; apply ps_axiom.
clear; induction extrules. simpl.
unfold ImpSystem. eauto using Irules.
right. apply IHextrules.
Qed.

Lemma valid_refl : forall phi, Valid (Implies phi phi).
intros; intro; intros; intro; assumption.
Qed.

Ltac axiom_helper extrules subst lhs rhs :=
  eapply ps_conseq;[eassumption| |eassumption];
  apply ps_conseq with
    (phi1' := (ApplyF subst lhs))
    (phi2' := (ApplyF subst rhs));
    clear;[valid_tac| |valid_tac];
  apply ps_subst; apply ps_axiom; clear;
  induction extrules;
    [simpl;unfold ImpSystem;eauto using Irules
    |right;assumption].

Lemma r_while' : forall extrules E' b' s' strict phi1 phi2,
  Valid (Implies phi1 (Pattern (plugS E' (SWhile b' s')))) ->
  Valid (Implies (Pattern (plugS E' (SIf b' (Seq s' (SWhile b' s')) Skip))) phi2)
  -> PS strict (List.fold_right cons_System ImpSystem extrules) phi1 phi2.
Proof.
  intros.
  axiom_helper extrules (Base.Update (Base.Update (Base.Update identity
      (existT _ E I) E')
      (existT _ s I) s')
      (existT _ b I) b')
    (Pattern (plugS E (SWhile b s)))
    (Pattern (plugS E (SIf b (Seq s (SWhile b s)) Skip))).
Qed.

Lemma r_leb' : forall extrules E' x' y' strict phi1 phi2,
  Valid (Implies phi1 (Pattern (plugB E' (BLe (ECon x') (ECon y'))))) ->
  Valid (Implies (Pattern (plugB E' (BCon (Zleb x' y')))) phi2)
  -> PS strict (List.fold_right cons_System ImpSystem extrules) phi1 phi2.
Proof.
  intros. axiom_helper extrules
      (Base.Update (Base.Update (Base.Update identity
      (existT _ E I) E')
      (existT _ x I) x')
      (existT _ y I) y')
    (Pattern (plugB E (BLe (ECon x) (ECon y))))
    (Pattern (plugB E (BCon (Zleb x y)))).
Qed.

Lemma r_if' : forall extrules E' s1' s2' strict phi1 phi2,
  Valid (Implies phi1 (Pattern (plugS E' (SIf (BCon (Bool false)) s1' s2')))) ->
  Valid (Implies (Pattern (plugS E' s2')) phi2)
  -> PS strict (List.fold_right cons_System ImpSystem extrules) phi1 phi2.
Proof.
  intros; axiom_helper extrules
      (Base.Update (Base.Update (Base.Update identity
      (existT _ E I) E')
      (existT _ s1 I) s1')
      (existT _ s2 I) s2')
    (Pattern (plugS E (SIf (BCon (Bool false)) s1 s2)))
    (Pattern (plugS E s2)).
Qed.

Lemma r_if_true' : forall extrules E' s1' s2' strict phi1 phi2,
  Valid (Implies phi1 (Pattern (plugS E' (SIf (BCon (Bool true)) s1' s2')))) ->
  Valid (Implies (Pattern (plugS E' s1')) phi2)
  -> PS strict (List.fold_right cons_System ImpSystem extrules) phi1 phi2.
Proof.
  intros. axiom_helper extrules
      (Base.Update (Base.Update (Base.Update identity
      (existT _ E I) E')
      (existT _ s1 I) s1')
      (existT _ s2 I) s2')
    (Pattern (plugS E (SIf (BCon (Bool true)) s1 s2)))
    (Pattern (plugS E s1)).
Qed.

Lemma r_plus' : forall extrules E' x' y' strict phi1 phi2,
  Valid (Implies phi1 (Pattern (plugE E' (EPlus (ECon x') (ECon y'))))) ->
  Valid (Implies (Pattern (plugE E' (ECon (PlusZ x' y')))) phi2)
  -> PS strict (List.fold_right cons_System ImpSystem extrules) phi1 phi2.
Proof.
  intros; axiom_helper extrules
      (Base.Update (Base.Update (Base.Update identity
      (existT _ E I) E')
      (existT _ x I) x')
      (existT _ y I) y')
    (Pattern (plugE E (EPlus (ECon x) (ECon y))))
    (Pattern (plugE E (ECon (PlusZ x y)))).
Qed.

Lemma r_assign' : forall extrules E' env' x' i' strict phi1 phi2,
  Valid (Implies phi1 (Pattern (plugS (cfgcS E' env') (SAssign x' (ECon i'))))) ->
  Valid (Implies (Pattern (plugS (cfgcS E' (Update env' x' i')) Skip)) phi2)
  -> PS strict (List.fold_right cons_System ImpSystem extrules) phi1 phi2.
Proof.
  intros; axiom_helper extrules
      (Base.Update (Base.Update (Base.Update (Base.Update identity
      (existT _ E I) E')
      (existT _ env I) env')
      (existT _ x I) x')
      (existT _ i I) i')
    (Pattern (plugS (cfgcS E env) (SAssign x (ECon i))))
    (Pattern (plugS (cfgcS E (Update env x i)) Skip)).
Qed.

Lemma r_seq' : forall extrules E' s' strict phi1 phi2,
  Valid (Implies phi1 (Pattern (plugS E' (Seq Skip s'))))
  ->
  Valid (Implies (Pattern (plugS E' s')) phi2)
  -> PS strict (List.fold_right cons_System ImpSystem extrules) phi1 phi2.
Proof.
  intros; axiom_helper extrules
      (Base.Update (Base.Update identity
      (existT _ E I) E')
      (existT _ s I) s')
    (Pattern (plugS E (Seq Skip s)))
    (Pattern (plugS E s)).
Qed.

Lemma add_add : forall x (i j : Z) m,
  PositiveMap.add x i (PositiveMap.add x j m)
  = PositiveMap.add x i m.
Transparent PositiveMap.add.
induction x; destruct m; simpl; congruence.
Qed.
Lemma build_diff : forall x (i : Z) y j, x <> y ->
  PositiveMap.add x i (PositiveMap.add y j (PositiveMap.Leaf _))
  = PositiveMap.add y j (PositiveMap.add x i (PositiveMap.Leaf _)).
Proof.
induction x; destruct y; simpl; intros; try congruence;
rewrite IHx; congruence.
Qed.

Lemma add_diff : forall x (i : Z) y j m, x <> y ->
  PositiveMap.add x i (PositiveMap.add y j m)
  = PositiveMap.add y j (PositiveMap.add x i m).
Proof.
induction x; destruct y; destruct m; simpl; try congruence.
intro;rewrite (build_diff x i y j);congruence.
intro;rewrite IHx;congruence.
intro;rewrite IHx;congruence.
intro;rewrite IHx;congruence.
Qed.

Definition pvi : T := Id (domains.var 1).
Definition pvj : T := Id (domains.var 2).

Lemma sum : entails false Mstep
  (And 
    (Pattern (Cfg
    (SWhile (BLe (ECon (Val 1%Z)) (EVar pvi))
      (Seq
        (SAssign pvi (EPlus (EVar pvi) (ECon (Val (-1)%Z))))
        (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1%Z))))))
    (Update (Update env pvi x) pvj y)))
  (Equals (Bool true) (Zleb (Val 0%Z) x)),
   Pattern (Cfg Skip
    (Update (Update env pvi (Val 0%Z))
      pvj (PlusZ x y)))).
Proof.
intros.
apply imp_partial_correctness.

remember (BLe (ECon (Val 1)) (EVar pvi)) as loopTest.
remember (Seq (SAssign pvi (EPlus (EVar pvi) (ECon (Val (-1)))))
              (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1)))))
  as loopBody.

apply ps_circ with
  (phi'' :=
    (And (Pattern
        (Cfg
          (SIf loopTest
            (Seq loopBody (SWhile loopTest loopBody))
            Skip)
          (Update (Update env pvi x) pvj y)))
    (Equals (Bool true) (Zleb (Val 0) x)))).

apply ps_lf;[|exact I].
apply (r_while' nil) with
  (E' := (cfgcS Shole (Update (Update env pvi x) pvj y)))
  (b' := loopTest)
  (s' := loopBody).
subst;solve[valid_tac].
subst;solve[valid_tac].

eapply ps_trans.
apply ps_lf;[|exact I].
rewrite HeqloopTest at 2.
apply (r_lookup' (_ ::nil)) with
  (E' := (ifcE (ler (Val 1) Ehole)
    (Seq loopBody (SWhile loopTest loopBody))
    Skip))
  (env' := (Update (Update env pvi x) pvj y))
  (x' := pvi).
subst;solve[valid_tac].
apply valid_refl.

eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_leb' (_::nil)) with
  (E' := cfgcB (ifcB Bhole
              (Seq loopBody (SWhile loopTest loopBody))
              Skip)
  (Update (Update env pvi x) pvj y))
  (x' := Val 1)
  (y' := (Lookup (Update (Update env pvi x) pvj y) pvi)).
subst;solve[valid_tac].
(* simplify the lookup now *)
instantiate (1 := 
  (Pattern (Cfg (SIf (BCon (Zleb (Val 1) x))
    (Seq loopBody (SWhile loopTest loopBody))
    Skip)
  (Update (Update env pvi x) pvj y)))).
subst;valid_tac.
apply some_inj in H. subst gamma.
repeat ((apply f_equal || apply f_equal2 || apply f_equal3);
  [|reflexivity..]);try reflexivity.

Transparent PositiveMap.find.
destruct val;reflexivity.
Opaque PositiveMap.find.

(* now, let's reason to split the assumption into
   two cases for x = 0 and 1 <= x *)
eapply ps_conseq with
  (phi1' :=
    (Or
      (And
        (Pattern
           (Cfg
              (SIf (BCon (Bool false))
                 (Seq loopBody (SWhile loopTest loopBody)) Skip)
              (Update (Update env pvi x) pvj y)))
        (Equals (Val 0) x))
      (And
        (Pattern
           (Cfg
              (SIf (BCon (Bool true))
                 (Seq loopBody (SWhile loopTest loopBody)) Skip)
              (Update (Update env pvi x) pvj y)))
        (Equals (Bool true) (Zleb (Val 1) x)))));
  [| |apply valid_refl].
(* subst;valid_tac without the ;trivial *)
unfold Valid. intros gamma rho.
setoid_rewrite <- SatImplies. 
setoid_rewrite <- SatOr.
setoid_rewrite <- SatAnd.
setoid_rewrite <- SatPattern.
setoid_rewrite <- SatEquals.
subst; unfold value; simpl. unfold lapply; simpl.
destruct 1 as [Hpat Hcond].
destruct_env.
apply some_inj in Hpat.
subst gamma.
apply M_inj in Hcond.
symmetry in Hcond.
destruct (Z_le_lt_eq_dec _ _ (Zle_bool_imp_le _ _ Hcond));
  [right | left].
assert (Zle_bool 1 val = true).
apply Zle_imp_le_bool.
change (Zsucc 0 <= val)%Z.
apply Zlt_le_succ.
assumption.
(* have 1 <= val *)
split; apply f_equal; congruence.

(* other case, have val = 0 *)
subst; split; apply f_equal;
 repeat ((apply f_equal || apply f_equal2 || apply f_equal3);
    [|reflexivity..]);(reflexivity||congruence).

apply ps_case.

(* Base case - x already equals zero *)

eapply ps_conseq.
apply valid_refl.

apply ps_lf;[|exact I].
apply (r_if' (_::nil)) with
  (E' := cfgcS Shole (Update (Update env pvi x) pvj y))
  (s1' := (Seq loopBody (SWhile loopTest loopBody)))
  (s2' := Skip).
subst;solve[valid_tac].
apply valid_refl.

unfold Valid, Satisfies, Implies; simpl.
unfold lapply; simpl; intros; destruct H; destruct_env.

apply some_inj in H.
apply M_inj in H0.
subst val0.

apply f_equal; subst gamma.
reflexivity.

(* circular case - 1 <= x.
   will decrement, then apply circular rule *)

eapply ps_trans.
(*
apply ps_trans with
  (phi2 := 
    (And
      (Pattern 
        (Cfg
          (SWhile loopTest loopBody)
          (Update (Update env pvi (PlusZ x (Val (-1))))
            pvj (PlusZ y (Val 1)))))
      (Equals (Bool true) (Zleb (Val 1) x)))).
*)

(* do the evaluation *)

apply ps_lf;[|exact I].
apply (r_if_true' (_::nil)) with
  (E' := (cfgcS Shole (Update (Update env pvi x) pvj y)))
  (s1' := (Seq loopBody (SWhile loopTest loopBody)))
  (s2' := Skip).
subst;solve[valid_tac].
apply valid_refl.

rewrite HeqloopBody at 2.

eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_lookup' (_::nil)) with
  (E' := (seqE (seqE (assigne pvi (plusl Ehole (ECon (Val (-1)))))
    (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1)))))
  (SWhile loopTest loopBody)))
  (env' := (Update (Update env pvi x) pvj y))
  (x' := pvi).
subst;solve[valid_tac].
apply valid_refl.

eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_plus' (_::nil)) with
  (E' :=
    (cfgcE (seqE (seqE (assigne pvi Ehole)
      (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1)))))
    (SWhile loopTest loopBody))
    (Update (Update env pvi x) pvj y)))
  (x' := x)
  (y' := Val (-1)).
subst;valid_tac.
apply some_inj in H; subst gamma.
repeat ((apply f_equal || apply f_equal2 || apply f_equal3);
  [|reflexivity..]);try reflexivity.
Transparent PositiveMap.find.
destruct val.
reflexivity.
reflexivity.
Opaque PositiveMap.find.
apply valid_refl.
      
eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_assign' (_::nil)) with
  (E' := seqS (seqS Shole (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1)))))
    (SWhile loopTest loopBody))
  (env' := (Update (Update env pvi x) pvj y))
  (x' := pvi)
  (i' := (PlusZ x (Val (-1)))).
subst;solve[valid_tac].
apply valid_refl.

eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_seq' (_::nil)) with
  (E' := (cfgcS
    (seqS Shole
      (SWhile loopTest loopBody))
    (Update (Update (Update env pvi x) pvj y) pvi
      (PlusZ x (Val (-1))))))
  (s' := (SAssign pvj (EPlus (EVar pvj) (ECon (Val 1))))).
subst; solve[valid_tac].
apply valid_refl.

eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_lookup' (_::nil)) with
  (E' :=
    (seqE (assigne pvj (plusl Ehole (ECon (Val 1))))
      (SWhile loopTest loopBody)))
  (env' := (Update (Update (Update env pvi x) pvj y) pvi
                 (PlusZ x (Val (-1)))))
  (x' := pvj)
  .
subst;solve[valid_tac].
apply valid_refl.

eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_plus' (_::nil)) with
  (E' :=
    cfgcE (seqE (assigne pvj Ehole)
      (SWhile loopTest loopBody))
    (Update (Update (Update env pvi x) pvj y) pvi
                 (PlusZ x (Val (-1)))))
  (x' := (Lookup
                 (Update (Update (Update env pvi x) pvj y) pvi
                    (PlusZ x (Val (-1)))) pvj))
  (y' := (Val 1))
  .
subst;solve[valid_tac].
apply valid_refl.

(* can't use r_assign' yet, or we'll capture x.
   so, substitute it to something else first *)
eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_assign' (_::nil)) with
  (E' := (seqS Shole (SWhile loopTest loopBody)))
  (env' := (Update (Update (Update env pvi x) pvj y) pvi
                 (PlusZ x (Val (-1)))))
  (x' := pvj)
  (i' := (PlusZ
                 (Lookup
                    (Update (Update (Update env pvi x) pvj y) pvi
                       (PlusZ x (Val (-1)))) pvj) (Val 1))).
subst; solve[valid_tac].
apply valid_refl.

eapply ps_trans.
apply ps_lf;[|exact I].
apply (r_seq' (_::nil)) with
  (E' := (cfgcS Shole
    (Update
      (Update (Update (Update env pvi x) pvj y) pvi
        (PlusZ x (Val (-1)))) pvj
      (PlusZ
        (Lookup
          (Update (Update (Update env pvi x) pvj y) pvi
            (PlusZ x (Val (-1)))) pvj) 
        (Val 1)))))
  (s' := (SWhile loopTest loopBody))
  .
subst;solve[valid_tac].

(* almost ready to apply circularity. 
   reason more carefully here to fold the lookup *)
instantiate (1:=
  (Pattern
    (Cfg (SWhile loopTest loopBody)
    (Update (Update env
      pvi (PlusZ x (Val (-1))))
      pvj (PlusZ y (Val 1)))))).
subst;valid_tac.
apply some_inj in H; subst gamma.
repeat ((apply f_equal || apply f_equal2 || apply f_equal3);
  [|reflexivity..]).
Transparent PositiveMap.find.
destruct val.
reflexivity.
destruct val2; reflexivity.
Opaque PositiveMap.find.

(* use consequence and the ciruclar hypothesis, 
   under a substitution x |-> x-1, y |-> y+1
   *)

apply ps_conseq with
  (phi1' :=
    (And
      (Pattern
        (Cfg (SWhile loopTest loopBody)
          (Update (Update env pvi (PlusZ x (Val (-1)))) pvj
            (PlusZ y (Val 1)))))
      (Equals (Bool true) (Zleb (Val 0) (PlusZ x (Val (-1)))))))
  (phi2' :=
    (Pattern (Cfg Skip (Update (Update env pvi (Val 0)) pvj
      (PlusZ (PlusZ x (Val (-1))) (PlusZ y (Val 1))))))).

unfold Valid; intros.
setoid_rewrite <- SatImplies.
setoid_rewrite <- SatAnd.
intuition.
clear -H1.
revert H1.
unfold Valid, Satisfies, Implies; simpl; unfold lapply; simpl; intros;
 destruct_env.
destruct (PositiveMap.find xv rho);[|destruct H1].
destruct s. destruct x;try solve[destruct H1].
apply M_inj in H1.
apply f_equal.
symmetry in H1 |- *.
setoid_rewrite <- Zle_is_le_bool in H1.
setoid_rewrite <- Zle_is_le_bool.
omega.

Focus 2.
unfold Valid; intros.
setoid_rewrite <- SatImplies.
valid_tac.
apply some_inj in H.
apply f_equal.
subst gamma.
apply f_equal.
replace (val0 + -1 + (val1 + 1))%Z with (val0 + val1)%Z by omega.
reflexivity.

(* now, take the circularity step under substitution *)
pose (subst :=
  (Base.Update
  (Base.Update (PositiveMap.empty T)
    (existT _ y I) (PlusZ y (Val 1)))
    (existT _ x I) (PlusZ x (Val (-1))))).
replace
  (And
    (Pattern
      (Cfg (SWhile loopTest loopBody)
        (Update (Update env pvi (PlusZ x (Val (-1)))) pvj
          (PlusZ y (Val 1)))))
    (Equals (Bool true) (Zleb (Val 0) (PlusZ x (Val (-1))))))
  with
    (ApplyF subst
      (And
        (Pattern
          (Cfg (SWhile loopTest loopBody)
            (Update (Update env pvi x) pvj y)))
        (Equals (Bool true) (Zleb (Val 0) x))))
    by (subst; reflexivity).
replace
  (Pattern
    (Cfg Skip
      (Update (Update env pvi (Val 0)) pvj
        (PlusZ (PlusZ x (Val (-1))) (PlusZ y (Val 1))))))
  with
    (ApplyF subst
      (Pattern
        (Cfg Skip
          (Update (Update env pvi (Val 0)) pvj
            (PlusZ x y)))))
    by (subst; reflexivity).
apply ps_subst.
apply ps_axiom.
left. reflexivity.
Qed.

Print Assumptions sum.