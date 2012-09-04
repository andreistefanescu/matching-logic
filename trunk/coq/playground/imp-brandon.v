Require Import ZArith.
Require Import List.

Set Implicit Arguments.

(* assert there are identifiers and maps.
   numbers and sorted association lists should have the same properties.
  
 *)
Parameters
  (Id : Set)
  (Map : Set -> Set)
  (bind : forall {K:Set} , Id -> K -> Map K -> Map K)
  (unbound : forall {K:Set}, Id -> Map K -> Prop)
  (empty_Map : forall {K:Set} , Map K)
  (empty_empty : forall {I} {K}, unbound I (@empty_Map K))
  .

(* generic relation stuff *)
Definition Relation X := X -> X -> Prop.
Inductive star {A : Type} (R : Relation A) : Relation A :=
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
Inductive Katom : Set :=
 | k_apply : label -> list K -> Katom
with K : Set :=
 | k_arrow : list Katom -> K
 .

(* The arrow *)
Definition kra (l r : K) : K :=
  match l, r with
  | k_arrow ls , k_arrow rs => k_arrow (ls ++ rs)
  end.
Infix "~>" := kra (at level 65, right associativity).
  (* binds a bit weaker than equality *)

(* The unit *)
Definition k_dot : K := k_arrow nil.

(* Proving the dot is a unit and the arrow associative *)
Ltac kopen := repeat match goal with
  | [ H : K |- _] => destruct H
  end.
Ltac kra_tac := intros; kopen; simpl;
  pose app_nil_r; pose app_ass; congruence.
Print Grammar constr.
Lemma kunit_left : forall k , k_dot ~> k = k. 
Proof. kra_tac. Qed.
Lemma kunit_right : forall k, k ~> k_dot = k.
Proof. kra_tac. Qed.
Lemma kra_assoc : forall x y z, (x ~> y) ~> z = x ~> (y ~> z).
Proof. kra_tac. Qed.

(* abbreviations for building terms *)
Notation k_app l args := (k_arrow (k_apply l args :: nil)).
Notation kapp0 l       := (k_app l nil).
Notation kapp1 l x     := (k_app l (x :: nil)).
Notation kapp2 l x y   := (k_app l (x :: y :: nil)).
Notation kapp3 l x y z := (k_app l (x :: y :: z :: nil)).

Notation k_id i   := (k_app (l_id i) nil).
Notation k_int i  := (k_app (l_int i) nil).
Notation k_bool b := (k_app (l_bool b) nil).

(* apply a relation at any position in a K *)
Inductive k_congruence (R : Relation K) : Relation K := 
 | here : forall k k', R k k' -> k_congruence R k k'
 | between_kra : forall l k k' r, k_congruence R k k' ->
     k_congruence R (l ~> k ~> r) (l ~> k' ~> r)
 | under_label : forall l args1 k k' args2, k_congruence R k k' ->
     k_congruence R
       (k_app l (args1 ++ k :: args2))
       (k_app l (args1 ++ k' :: args2))
 .

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

Definition is_value K :=
  match K with
  | k_bool _ => true
  | k_int _ => true
  | _ => false
  end.

Inductive configuration : Set :=
  Conf { k : K ; state : Map K}.

(* lift a relation on K to a relation on
   imp configurations,
   by letting it apply in the k cell or in map values *)
Inductive complete_k (R : Relation K)
  : Relation configuration :=
 | in_k : forall k k' env, R k k' ->
     complete_k R
       {| k := k ; state := env |}
       {| k := k' ; state := env |}
 | in_map : forall k0 x k k' env, unbound x env -> R k k' ->
     complete_k R
       {| k := k0 ; state := bind x k env |}
       {| k := k0 ; state := bind x k' env |}
 .

(* The rules of imp that do not mention cells *)
Inductive free_transitions : Relation K :=
 | plus_val : forall x y,
     free_transitions
       (k_plus (k_int x) (k_int y))
       (k_int (x + y)%Z)
 | div_val : forall x y, y <> 0%Z ->
     free_transitions
        (k_div (k_int x) (k_int y))
        (k_int (x / y)%Z)
 | le_val : forall x y,
     free_transitions
        (k_le (k_int x) (k_int y))
        (k_bool (Zle_bool x y))
 | not_val : forall b,
     free_transitions
        (k_not (k_bool b))
        (k_bool (negb b))
 | and_val_t : forall e,
     free_transitions
        (k_and (k_bool true) e) 
        e
 | and_val_f : forall e,
     free_transitions
        (k_and (k_bool false) e) 
        (k_bool false)
 | skip_vanish : (* structural *)
     free_transitions
        k_skip
        k_dot
 | stmt_sequence : forall s1 s2,
     free_transitions
        (k_seq s1 s2)
        (kra s1 s2)
 | if_true : forall s1 s2,
     free_transitions
        (k_if (k_bool true) s1 s2)
        s1
 | if_false : forall s1 s2,
     free_transitions
        (k_if (k_bool false) s1 s2)
        s1
 .

(* The rules of imp which are anchored to cells *)
Inductive ctx_transition : Relation configuration :=
 | lookup : forall X I rest env, unbound X env ->
     ctx_transition {| k := kra (k_id X) rest
                     ; state := bind X (k_int I) env |}
                    {| k := kra (k_int I) rest
                     ; state := bind X (k_int I) env |}
 | assignment : forall X I rest old env,  unbound X env ->
     ctx_transition {| k := kra (k_assign X (k_int I)) rest
                    ; state := bind X old env |}
                    {| k := kra k_dot rest
                    ; state := bind X (k_int I) env |}
 | while : forall b s rest env,
     ctx_transition {| k := kra (k_while b s) rest
                     ; state := env |}
                    {| k := kra (k_if b (k_seq s (k_while b s)) k_skip)
                       rest ; state := env |} (* structural *)
 | program_still_vars : forall (x : Id) xs b env, unbound x env ->
     ctx_transition {| k := k_pgm (k_cons (k_id x) xs) b
                     ; state := env |}
                    {| k := k_pgm xs b
                     ; state := bind x (k_int 0) env |}
 | program_no_vars : forall b env,
     ctx_transition {| k := k_pgm k_nil b ; state := env |}
                    {| k := b             ; state := env |}
 .

(* A computation step uses one or the other of these rules *)
Inductive computation_step : Relation configuration :=
 | cell_step : forall c c',
     ctx_transition c c' ->
       computation_step c c'
 | deep_step : forall c c',
     complete_k (k_congruence free_transitions) c c' ->
       computation_step c c'
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

(* An abbreviation for taking a step to be applied at the
   head of the K cell, and framing in the rest of the k
   cell and the store *)
Definition k_step R k k' := forall rest env,
  R {| k := kra k rest ;  state := env |}
    {| k := kra k' rest ; state := env |}.

Inductive heating_transitions : Relation configuration :=
 | plus_heat_l : forall l r , is_value l = false ->
       k_step heating_transitions
           (k_plus l r)
           (kra l (k_plus_H_e r))
 | plus_cool_l : forall lv r, is_value lv = true ->
       k_step heating_transitions
           (kra lv (k_plus_H_e r))
           (k_plus lv r)
 | plus_heat_r : forall l r, is_value r = false ->
       k_step heating_transitions
           (k_plus l r)
           (kra r (k_plus_e_H l))
 | plus_cool_r : forall lv rv,
       is_value lv = true -> is_value rv = true ->
       k_step heating_transitions
           (kra rv (k_plus_e_H lv))
           (k_plus lv rv)
 | le_heat_l : forall l r, is_value l = false ->
       k_step heating_transitions
           (k_le l r)
           (kra l (k_le_H_e r))
 | le_cool_l : forall lv r, is_value lv = true ->
       k_step heating_transitions
           (kra lv(k_le_H_e r))
           (k_le lv r)
 | le_heat_r : forall lv r,
       is_value lv = true -> is_value r = false ->
       k_step heating_transitions
           (k_le lv r)
           (kra r (k_le_v_H lv))
 | le_cool_r : forall lv rv,
       is_value lv = true -> is_value rv = true ->
       k_step heating_transitions
           (kra rv (k_le_v_H lv))
           (k_le lv rv)
 | not_heat : forall b, is_value b = false ->
       k_step heating_transitions
           (k_not b)
           (kra b k_not_H)
 | not_cool : forall bv, is_value bv = true ->
       k_step heating_transitions
           (kra bv k_not_H)
           (k_not bv)
 | and_heat : forall b e, is_value b = false ->
       k_step heating_transitions
           (k_and b e)
           (kra b (k_and_H_e e))
 | and_cool : forall bv e, is_value bv = true ->
       k_step heating_transitions
           (kra bv (k_and_H_e e))
           (k_and bv e)
 | assign_heat : forall x e, is_value e = false ->
       k_step heating_transitions
           (k_assign x e)
           (kra e (k_assign_id_H x))
 | assign_cool : forall x v, is_value v = true ->
       k_step heating_transitions
           (kra v (k_assign_id_H x))
           (k_assign x v)
 | if_heat : forall c t e, is_value c = false ->
       k_step heating_transitions
           (k_if c t e)
           (kra c (k_if_H_e_e t e))
 | if_cool : forall cv t e, is_value cv = true ->
       k_step heating_transitions
           (kra cv (k_if_H_e_e t e))
           (k_if cv t e)
 .

(* Define one computation step as any number of structural
   rules followed by a single computation step *)
Inductive imp_step : Relation configuration :=
  | Imp_step : forall c c1 c2,
      star heating_transitions c c1 ->
      computation_step c1 c2 ->
      imp_step c c2.

Definition imp_run := star imp_step.

(* A little example computation, manually taking steps *)
Parameter var_x : Id.
Definition example_env := bind var_x (k_int 18) empty_Map.

Theorem example :
  imp_run (Conf (k_plus (k_id var_x) (k_int 12)) example_env)
          (Conf (k_int 30) example_env).

Definition one_heat {x} {y} (step : heating_transitions x y)
  := trans _ step (refl heating_transitions _).

eapply trans. econstructor. eapply one_heat.
apply (plus_heat_l (k_id var_x) (k_int 12) (refl_equal _) k_dot example_env).
apply cell_step.
apply (@lookup var_x 18 (k_plus_H_e (k_int 12)) empty_Map).
  apply empty_empty.

eapply trans. econstructor. eapply one_heat.
apply (plus_cool_l (k_int 18) (k_int 12) (refl_equal _) k_dot example_env).
simpl.
apply deep_step. apply in_k. apply here. apply plus_val.

apply refl.
Qed.