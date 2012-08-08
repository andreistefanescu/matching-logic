Require Import ZArith.
Require Import List.
Require Import FMapInterface.
Require FMapPositive.

Open Scope Z_scope.

Set Implicit Arguments.

Definition Id : Set := positive.

Module IdMap := FMapPositive.PositiveMap.

Definition find0 (v:Id) (m:(IdMap.t Z)) : Z :=
  match IdMap.find v m with
  | Some r => r
  | None => 0%Z
  end.

Definition findInLem (v:Id) {elt:Type} (m:IdMap.t elt) :
  IdMap.find v m = None -> IdMap.mem v m = true -> False.
intros.
  apply IdMap.mem_2 in H0. destruct H0.
  apply IdMap.find_1 in H0. congruence.
Defined.

(* lookup which always succeeds, given membership predicate *)
Definition findIn (v:Id) {elt:Type} (m:IdMap.t elt) :
  IdMap.mem v m = true -> elt :=
match IdMap.find v m as r
  return IdMap.find v m = r -> IdMap.mem v m = true -> elt with
  | Some r => fun _ _ => r
  | None => fun H1 H2 => False_rect _ (findInLem v m H1 H2)
  end (eq_refl _).

Definition Map : Type -> Type := IdMap.t .
Definition bind : forall {K:Set} , Id -> K -> Map K -> Map K := IdMap.add.
Definition unbound : forall {K:Set}, Id -> Map K -> Prop :=
  fun _ v m => IdMap.mem v m = false.
Definition empty_Map : forall {K:Set} , Map K := IdMap.empty.
Implicit Arguments empty_Map [[K]].
Lemma empty_empty : forall {I} {K}, unbound I (@empty_Map K).
  intros. case_eq (IdMap.mem I (@empty_Map K)).
(* absurd true case *)
  generalize (@IdMap.empty_1 K I).
  unfold IdMap.Empty, unbound, empty_Map, IdMap.In.
  intros. exfalso. apply IdMap.mem_2 in H0. unfold IdMap.In in H0.
  destruct H0. apply (H x H0).
(* false case of split *)
  intro.  assumption.
Qed.

Check relation.

Print relation.

(* generic relation stuff *)
Inductive star {A : Type} (R : relation A) : relation A :=
  | refl : forall a, star R a a
  | trans : forall b a c, R a b -> star R b c -> star R a c
  .
Implicit Arguments trans [[A] R a c].

(* all labels. H stands for HOLE *)
Inductive label : Set :=
(* labels for injecting primitives *)
 | l_id (i : Id)
 | l_bool (b : bool)
 | l_int (n : Z)
(* labels for translating list syntax *)
 | l_cons
 | l_nil
(* labels from imp syntax *)
 | l_plus | l_plus_H_e | l_plus_e_H
 | l_div | l_div_H_e | l_div_e_H
 | l_le | l_le_H_e | l_le_v_H
 | l_not | l_not_H
 | l_and | l_and_H_e
 | l_skip
 | l_assign | l_assign_id_H
 | l_seq
 | l_if | l_if_H_e_e
 | l_while
 | l_pgm
 .

(* Defining the sort K.
 To support exact associativity,
 every K has a list of applied labels.

 The arrow kra and the unit k_dot will
 be derived terms
*)
Inductive K : Set :=
 | k_apply : label -> list K -> K.

(* separate from lists, because a notation for
   (@nil K) cannot be used in patterns *)
Inductive Kseq : Set :=
  | k_dot
  | k_kra1 : K -> Kseq -> Kseq.

Delimit Scope K_scope with K.
Open Scope K_scope.
Infix "~>" := k_kra1 (at level 65, right associativity) : K_scope.
Definition kitem k : Kseq := k ~> k_dot.

Coercion kitem : K >-> Kseq.
Reserved Notation "x ~~> y" (at level 65, right associativity).
Fixpoint kra k1 k2 :=
  match k1 with
  | k_dot => k2
  | k ~> k1' => k ~> (k1' ~~> k2)
  end
where "x ~~> y" := (kra x y) : K_scope.


(* Proving the dot is a unit and the arrow associative *)
Lemma kunit_left : forall k , k_dot ~~> k = k. 
Proof. reflexivity. Qed.
Lemma kunit_right : forall k, k ~~> k_dot = k.
Proof. induction k; simpl; congruence. Qed.
Lemma kra_assoc : forall x y z, (x ~~> y) ~~> z = x ~~> (y ~~> z).
Proof. induction x; simpl; congruence. Qed.

(* abbreviations for building K *)
Notation kapp0 l       := (k_apply l nil).
Notation kapp1 l x     := (k_apply l (x :: nil)).
Notation kapp2 l x y   := (k_apply l (x :: y :: nil)).
Notation kapp3 l x y z := (k_apply l (x :: y :: z :: nil)).

Notation k_id i   := (k_apply (l_id i) nil).
Definition k_id_d i := k_id i.
Coercion k_id_d : Id >-> K.
Notation k_int i  := (k_apply (l_int i) nil).
Definition k_int_d i := k_int i.
Coercion k_int_d : Z >-> K.
Notation k_bool b := (k_apply (l_bool b) nil).

(* abbreviations for syntax of IMP *)
Notation k_plus l r := (kapp2 l_plus l r).
Notation k_div l r := (kapp2 l_div l r).
Notation k_le l r := (kapp2 l_le l r).
Notation k_not b := (kapp1 l_not b).
Notation k_and l r := (kapp2 l_and l r).
Notation k_skip := (kapp0 l_skip).
Notation k_seq s1 s2 := (kapp2 l_seq s1 s2).
Notation k_if c t e := (kapp3 l_if c t e).
Notation k_assign i e := (kapp2 l_assign (k_id i) e).
Notation k_while c e := (kapp2 l_while c e).
Notation k_pgm ids b := (kapp2 l_pgm ids b).
Notation k_cons c r := (kapp2 l_cons c r).
Notation k_nil := (kapp0 l_nil).

Delimit Scope imp_scope with imp.
Notation "x + y" := (k_plus (x:K) (y:K) : K) : imp_scope .
Notation "x / y" := (k_div (x:K) (y:K) : K) : imp_scope .
Notation "x <= y" := (k_le (x:K) (y:K) : K) : imp_scope .
Notation "x && y" := (k_and (x:K) (y:K) : K) : imp_scope.
Notation "'if' c 'then' t 'else' e 'fi'" :=
  (k_if (c:K) (t:K) (e:K) : K) : imp_scope.
Notation "i <- e" := (k_assign i (e:K) : K)
  (at level 30 , no associativity) : imp_scope.
Notation "'while' c 'do' e 'end'"
  := (k_while (c:K)%imp (e:K)%imp : K) : imp_scope.

Print Grammar constr.
 
Definition is_value (k : K) :=
  match k with
  | k_bool _ => true
  | k_int _ => true
  | _ => false
  end.

Inductive configuration : Type :=
  Conf { k : Kseq ; state : Map Z }.

(* An abbreviation for taking a step to be applied at the
   head of the K cell, and framing in the rest of the k
   cell and the store *)
Notation k_step R k k' := (forall rest env,
  R {| k := k ~> rest ;  state := env |}
    {| k := k' ~~> rest ; state := env |}).

Inductive computation_step : relation configuration :=
(* The rules of imp that do not mention cells *)
 | plus_val : forall x y,
     k_step computation_step
       (k_plus (k_int x) (k_int y))
       (k_int (x + y)%Z)
 | div_val : forall x y, y <> 0%Z ->
     k_step computation_step
        (k_div (k_int x) (k_int y))
        (k_int (x / y)%Z)
 | le_val : forall x y,
     k_step computation_step
        (k_le (k_int x) (k_int y))
        (k_bool (Zle_bool x y))
 | not_val : forall b,
     k_step computation_step
        (k_not (k_bool b))
        (k_bool (negb b))
 | and_val_t : forall e,
     k_step computation_step
        (k_and (k_bool true) e)
        e
 | and_val_f : forall e,
     k_step computation_step
        (k_and (k_bool false) e) 
        (k_bool false)
 | skip_vanish : (* structural *)
     k_step computation_step
        k_skip
        k_dot
 | stmt_sequence : forall s1 s2,
     k_step computation_step
        (k_seq s1 s2)
        (s1 ~> s2)
 | if_true : forall s1 s2,
     k_step computation_step
        (k_if (k_bool true) s1 s2)
        s1
 | if_false : forall s1 s2,
     k_step computation_step
        (k_if (k_bool false) s1 s2)
        s2
(* The rules of imp which are anchored to cells *)
 | lookup : forall X rest env (Xin : IdMap.mem X env = true),
(* use find0 rather than findIn becaues apply handles
   dependent arguments badly *)
     computation_step
       {| k := k_id X ~> rest
        ; state := env |}
       {| k := k_int (find0 X env) ~> rest
        ; state := env |}
 | assignment : forall X I rest env, IdMap.mem X env = true ->
     computation_step
       {| k := k_assign X (k_int I) ~> rest
        ; state := env |}
       {| k := rest
        ; state := bind X I env |}
 | s_while : forall b s rest env,
     computation_step
       {| k := k_while b s ~> rest
        ; state := env |}
       {| k := k_if b (k_seq s (k_while b s)) k_skip ~> rest
        ; state := env |} (* structural *)
 | program_still_vars : forall (x : Id) xs b env, unbound x env ->
     computation_step
       {| k := k_pgm (k_cons (k_id x) xs) b ~> k_dot
        ; state := env |}
       {| k := k_pgm xs b ~> k_dot
        ; state := bind x 0%Z env |}
 | program_no_vars : forall b env,
     computation_step
       {| k := k_pgm k_nil b ~> k_dot ; state := env |}
       {| k := b ~> k_dot             ; state := env |}
 .

(* Abbreviations for the freezers *)
Definition k_plus_H_e r := kapp1 l_plus_H_e r.
Definition k_plus_e_H l := kapp1 l_plus_e_H l.
Definition k_le_H_e r := kapp1 l_le_H_e r.
Definition k_le_v_H lv := kapp1 l_le_v_H lv.
Definition k_not_H := kapp0 l_not_H.
Definition k_and_H_e r := kapp1 l_and_H_e r.
Definition k_assign_id_H x := kapp1 l_assign_id_H (k_id x).
Definition k_if_H_e_e t e := kapp2 l_if_H_e_e t e.

Notation kseq_step R k k' := (forall env,
  R {| k := k ;  state := env |}
    {| k := k' ; state := env |}).

Inductive heating_transitions : relation configuration :=
 | plus_heat_l : forall l r, is_value l = false ->
       k_step heating_transitions
           (k_plus l r)
           (l ~> k_plus_H_e r)
 | plus_cool_l : forall lv r, is_value lv = true -> forall rest env,
       heating_transitions
           {| k := lv ~> k_plus_H_e r ~> rest ; state := env |}
           {| k := k_plus lv r ~> rest ; state := env |}
 | plus_heat_r : forall l r, is_value r = false ->
       k_step heating_transitions
           (k_plus l r)
           (r ~> k_plus_e_H l)
 | plus_cool_r : forall l rv,
       is_value rv = true -> forall rest env,
       heating_transitions
         {| k := rv ~> k_plus_e_H l ~> rest ; state := env |}
         {| k := k_plus l rv ~> rest ; state := env |}
 | le_heat_l : forall l r, is_value l = false ->
       k_step heating_transitions
           (k_le l r)
           (l ~> k_le_H_e r)
 | le_cool_l : forall lv r, is_value lv = true -> forall rest,
       kseq_step heating_transitions
           (lv ~> k_le_H_e r ~> rest)
           (k_le lv r ~> rest)
 | le_heat_r : forall lv r,
       is_value lv = true -> is_value r = false ->
       k_step heating_transitions
           (k_le lv r)
           (r ~> k_le_v_H lv)
 | le_cool_r : forall lv rv,
       is_value lv = true -> is_value rv = true -> forall (rest : Kseq),
       kseq_step heating_transitions
           (rv ~> k_le_v_H lv ~> rest)
           (k_le lv rv ~> rest)
 | not_heat : forall b, is_value b = false ->
       k_step heating_transitions
           (k_not b)
           (b ~> k_not_H)
 | not_cool : forall bv, is_value bv = true -> forall rest,
       kseq_step heating_transitions
           (bv ~> k_not_H ~> rest)
           (k_not bv ~> rest)
 | and_heat : forall b e, is_value b = false ->
       k_step heating_transitions
           (k_and b e)
           (b ~> k_and_H_e e)
 | and_cool : forall bv e, is_value bv = true -> forall rest,
       kseq_step heating_transitions
           (bv ~> k_and_H_e e ~> rest)
           (k_and bv e ~> rest)
 | assign_heat : forall x e, is_value e = false ->
       k_step heating_transitions
           (k_assign x e)
           (e ~> k_assign_id_H x)
 | assign_cool : forall x (v : K), is_value v = true -> forall rest,
       kseq_step heating_transitions
           (v ~> k_assign_id_H x ~> rest)
           (k_assign x v ~> rest)
 | if_heat : forall c t e, is_value c = false ->
       k_step heating_transitions
           (k_if c t e)
           (c ~> k_if_H_e_e t e)
 | if_cool : forall cv t e, is_value cv = true -> forall rest,
       kseq_step heating_transitions
           (cv ~> k_if_H_e_e t e ~> rest)
           (k_if cv t e ~> rest)
 .

(*
Add Parametric Relation : configuration heating_transitions as heating.
Add Parametric Morphism : (star heating_transitions)
  with signature heating_transitions --> eq ==> impl
  as star_heat.
Proof.
unfold impl; intros; eapply trans; eassumption.
Qed.
Add Parametric Morphism : (star heating_transitions)
  with signature heating_transitions ++> eq ==> flip impl
  as star_heat_flip.
Proof.
unfold impl; intros; eapply trans; eassumption.
Qed.
*)

Hint Immediate
  plus_heat_l plus_cool_l
  plus_heat_r plus_cool_r
  le_heat_l le_cool_l
  le_heat_r le_cool_r
  not_heat not_cool
  and_heat and_cool  
  assign_heat assign_cool
  if_heat if_cool
  : heating.

(* Define one computation step as any number of structural
   rules followed by a single computation step *)
Inductive imp_step : relation configuration :=
  | Imp_step : forall c c1 c2,
      star heating_transitions c c1 ->
      computation_step c1 c2 ->
      imp_step c c2.

Definition imp_run := star imp_step.

(* A little example computation, manually taking steps *)
Definition var_x : Id := 1%positive.
Definition example_env := bind var_x 18%Z empty_Map.

Print Conf.

Check {| k := k_dot ; state := empty_Map |}.


Theorem example :
  imp_run (Conf ((var_x + 12)%imp ~> k_dot) example_env)
          (Conf (30 ~> k_dot) example_env).

Ltac heat := (repeat (eapply trans;[solve[auto with heating]|];instantiate;simpl);apply refl).

simpl;eapply trans;[eapply Imp_step;[heat|constructor; reflexivity]|].
simpl;eapply trans;[eapply Imp_step;[heat|constructor; reflexivity]|].
apply refl.
Qed.

Theorem example2 :
  imp_run (Conf (((1 + 2) + (3 + 4))%imp ~> k_dot)
           example_env)
          (Conf (10 ~> k_dot)
           example_env).
repeat (instantiate;simpl;eapply trans;[eapply Imp_step;[heat|constructor; reflexivity]|]).
apply refl.
Qed.

Theorem example3 :
  imp_run (Conf (((1 + var_x) + (3 + 4))%imp ~> k_dot)
           example_env)
          (Conf (k_int 26 ~> k_dot)
           example_env).
repeat (instantiate;simpl;eapply trans;[eapply Imp_step;[heat|constructor; reflexivity]|]).
apply refl.
Qed.


Definition var_y : Id := 2%positive.
Definition example_env2 :=
  bind var_y 0 (bind var_x 3 empty_Map).
Definition example_pgm :=
  (k_seq
    (while 0 <= var_x do k_seq
       (var_y <- (var_y + var_x))
       (var_x <- (var_x + -1%Z)) end)
   (var_y:K))%imp.

Definition example_pgm' :=
  ((while 0 <= var_x do k_seq
       (var_y <- (var_y + var_x))
       (var_x <- (var_x + -1%Z)) end)%imp ~>
   (var_y:K)%imp ~> k_dot).

Unset Printing All.
Theorem example4 : exists env', 
  imp_run (Conf example_pgm example_env2)
          (Conf 6%Z env').
eexists.
repeat (instantiate;simpl;eapply trans;[eapply Imp_step;[heat|constructor; reflexivity]|]).
apply refl.
Qed.

Definition myenv (n m : Z) :=
  bind var_y m (bind var_x n empty_Map).

Theorem example5 :
  forall n' : nat,
    forall n m : Z,
      n = Z_of_nat n' ->
      exists env',
        imp_run
          (Conf example_pgm' (myenv n m))
          (Conf (n * (n + 1) / 2 + m)%Z env').
induction n'.
intros.
subst n.
intros.
eexists.
simpl.
eapply trans.
eapply Imp_step.
unfold example_pgm.
heat.
constructor.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
reflexivity.
eapply trans.
eapply Imp_step.
heat.
constructor.
unfold find0.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
unfold Zle_bool.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
eapply trans.
eapply Imp_step.
unfold myenv.
heat.
simpl.
constructor.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
reflexivity.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
reflexivity.
unfold find0.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
reflexivity.
eapply trans.
eapply Imp_step.
heat.
constructor.
reflexivity.
eapply trans.
eapply Imp_step.
heat.
constructor.
unfold find0; simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
reflexivity.
eapply trans.
eapply Imp_step.
heat.
constructor.
eapply trans.
eapply Imp_step.
heat.
constructor.
reflexivity.
eapply trans.
eapply Imp_step.
heat.
constructor.
unfold find0; simpl.
eapply trans.
unfold Zle_bool; simpl.
econstructor.
heat.
constructor.
unfold Zle_bool; simpl.
eapply trans.
econstructor.
heat.
constructor.
simpl.
eapply trans.
econstructor.
heat.
constructor.
simpl.
reflexivity.
unfold find0; simpl.
replace (m + 0) with m.
apply refl.
rewrite Zplus_0_r; reflexivity.

intros.
specialize (IHn' (n - 1)).
assert (Heq : n - 1 = Z_of_nat n').
subst n.
replace (S n') with (n' + 1)%nat.
rewrite inj_plus.
simpl.
rewrite <- Zplus_comm.
rewrite Zminus_plus.
reflexivity.
SearchAbout plus.
rewrite plus_comm.
simpl.
reflexivity.
specialize (IHn' (m + n) Heq).

assert (n > 0).
subst n.
reflexivity.

elim IHn'.
intros env'.
intros Hind.
clear IHn'.

clear H.
clear Heq.
clear n'.

eexists.
simpl.
eapply trans.
eapply Imp_step.
unfold example_pgm.
heat.
constructor.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
reflexivity.
eapply trans.
eapply Imp_step.
heat.
constructor.
unfold find0.
simpl.
replace (Zle_bool 0 n) with true.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
eapply trans.
eapply Imp_step.
unfold myenv.
heat.
simpl.
constructor.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
reflexivity.
unfold find0.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
reflexivity.
unfold find0.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
reflexivity.
eapply trans.
eapply Imp_step.
heat.
constructor.
reflexivity.
unfold find0; simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
simpl.
eapply trans.
eapply Imp_step.
heat.
constructor.
reflexivity.
unfold example_pgm' in Hind.
unfold myenv in Hind.
simpl.
simpl in Hind.
replace (n + -1) with (n - 1).
replace ((n - 1) * (n - 1 + 1) / 2 + (m + n)) with (n * (n + 1) / 2 + m) in Hind.
unfold imp_run in Hind.
apply Hind.

replace (m + n) with (n + m).
rewrite Zplus_assoc.
apply Zplus_eq_compat.
SearchAbout Zmult.
apply Zmult_reg_r with (p := 2).
compute.
intros.
inversion H.
SearchAbout Zdiv.

assert (forall n, Zeven (n * (n + 1))).
intros.
case (Zeven_dec n0).
intros.
replace n0 with (2 * Zdiv2 n0).



rewrite Zmult_plus_distr_l.
assert (forall p, p / 2 * 2 = p).
intros.
clear Hind.