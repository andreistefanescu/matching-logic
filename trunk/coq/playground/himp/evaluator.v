Require Import kstyle.
Require Import domains.

Require Import ZArith.
Require Import String.
Require Import List.

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

Functional Scheme str_split_ind := Induction for str_split Sort Prop.

Lemma str_split_sound k {V} (m : Map string V) :
  match str_split k m with
    | Some (v, m') => m ~= k |-> v :* m'
    | None => True
  end.
Proof.
functional induction (str_split k m);auto;try equate_maps;
match goal with [H : str_split ?x ?m = _, IH : match str_split ?x ?m with None => _ | _ => _ end
              |- _] => rewrite H in IH; rewrite IH end;
equate_maps.
Qed.

Lemma str_split_sound' k {V} (v : V) m m' :
  str_split k m = Some (v, m') -> m ~= k |-> v :* m'.
Proof.
pose proof (str_split_sound k m).
intro.
rewrite H0 in H.
assumption.
Qed.

Inductive HasKey {K V} (x : K) : Map K V -> Prop :=
  | key_here : forall v, HasKey x (x |-> v)
  | key_left : forall env env', HasKey x env -> HasKey x (env :* env')
  | key_right : forall env env', HasKey x env' -> HasKey x (env :* env')
  .

Lemma transport_has_key {K V} x (env env' : Map K V) :
  env ~= env' -> (HasKey x env <-> HasKey x env').
Proof.
induction 1; split;intros;
repeat match goal with [H : HasKey _ ?V |- _] => (is_var V;fail 1) || (inversion H; clear H; subst) end;
repeat match goal with [H : _ <-> _ |- _] => destruct H end;
eauto using key_left, key_right, key_here.
Qed.

Definition has_key {K V} (x : K) (m : Map K V) :=
  exists v env', m ~= x |-> v :* env'.

Lemma rep {K V} x (env : Map K V) :
  has_key x env -> HasKey x env.
Proof.
destruct 1 as [v [env' H]].
apply (transport_has_key x) in H.
apply H.
eauto using key_left, key_right, key_here.
Qed.

Lemma rep_inv {K V} x (env : Map K V) :
  HasKey x env -> has_key x env.
induction 1.
eexists. eexists. symmetry. apply equivUnit.
destruct IHHasKey as [v [env'' IH]].
exists v. exists (env'' :* env').
rewrite IH. equate_maps.
destruct IHHasKey as [v [env'' IH]].
exists v. exists (env :* env'').
rewrite IH. equate_maps.
Qed.

Lemma lemm1 {K V} x :
  @has_key K V x mapEmpty -> False.
intros.
apply rep in H.
inversion H.
Qed.

Lemma lemm2 {K V} x v x2 : @has_key K V x2 (x |-> v) -> x = x2.
Proof.
intros. apply rep in H.
inversion H. auto.
Qed.

Lemma lemm3 {K V} x (env1 env2 : Map K V) :
  has_key x (env1 :* env2) -> has_key x env1 \/ has_key x env2.
Proof.
intros.
apply rep in H.
inversion H; subst;
auto using rep_inv.
Qed.

(* Without enforcing definedness there might be duplicate labels, but str_split finds some label *)
Lemma str_split_completeish : forall x {V} (env : Map string V),
  has_key x env -> if str_split x env then True else False.
Proof.
intros.
induction env.

apply lemm1 in H. auto.
apply lemm2 in H. simpl. destruct (string_dec x k); auto.
apply lemm3 in H. simpl.
destruct (str_split x env1).
destruct p; destruct m; trivial.
destruct (str_split x env2).
destruct p. trivial.
intuition.
Qed.

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
match goal with [H : str_split _ _ = _ |- _] => apply str_split_sound' in H;eassumption end).
Qed.

Lemma eval_completeish : forall cfg cfg', kstep cfg cfg' ->
                                          match eval cfg with
                                                         Some cfg'' => kstep cfg cfg''
                                                       | None => False end.
Proof.
Ltac good_split x env :=
  let H0 := fresh in
  assert (has_key x env) as H0 by firstorder;
  apply str_split_completeish in H0;
  pose proof (str_split_sound x env);
  destruct (str_split x env) as [[]|];[clear H0|solve[destruct H0]].

intros;destruct H;simpl;repeat match goal with
  | [H : ?env ~= ?x |-> _ :* _ |- context [match str_split ?x ?env with None => _ | _ => _ end]] =>
    good_split x env
  | [|- kstep _ _] => econstructor (eassumption || reflexivity)
  | [H : Zneq_bool ?x ?y = _ |- context [if Zneq_bool ?x ?y then _ else _]] => rewrite H
  | [|- context [match ?e with EVar _ => _ | _ => _ end]] => destruct e; try discriminate
  | [|- context [match ?b with BCon _ => _ | _ => _ end]] => destruct b; try discriminate
end.
Qed.