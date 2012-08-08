Require Import List.

(* for simplicity, I just work with natural numbers *)
Definition int := nat.

(* identifiers are simply build from integers by applying a constructor *)
Inductive id : Type :=
  Id : int -> id.

(* equality on integers *)
Fixpoint beq_int (n m : int) : bool :=
  match (n, m) with
    | (0, 0) => true
    | (S _, 0) => false
    | (0, S _) => false
    | (S n', S m') => beq_int n' m'
  end.

Definition bneq_int (n m : int) : bool := negb (beq_int n m).

(* equality on ids *)

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_int n1 n2
  end.

Definition bneq_id X1 X2 := negb (beq_id X1 X2).

(* this type should be automatically generated from a corresponding K definition *)

Inductive K : Type :=
  (* AExp *)
  | c_int : int -> K                    (* need to infer constructor name "c_int" here *)
  | c_id : id -> K
  | c_plus : K -> K -> K                (* even more inference for _+_ *)
  | c_div : K -> K -> K

  (* BExp *)
  | c_bool : bool -> K
  | c_le : K -> K -> K
  | c_not : K -> K
  | c_and : K -> K -> K

  (* Stmt *)
  | c_skip : K
  | c_assignment : K -> K -> K
  | c_seq : K -> K -> K
  | c_ifthenelse : K -> K -> K -> K
  | c_while : K -> K -> K

  (* Pgm *)
  | c_pgm : list id -> K -> K

(*
   (C1 ~> C2) ~> C3
   C1 ~> (C2 ~> C3)
*)

  (* the ~> operation and the corresponding hole *)
  | k_hole : K
  | k_list : K -> K -> K
  | k_nothing : K.

Definition is_value (k : K) : bool :=
  match k with
    | c_bool _ => true
    | c_int _ => true
    | _ => false
  end.

Definition is_int (k : K) : bool :=
  match k with
    | c_int _ => true
    | _ => false
  end.

Definition cfg : Type := prod K (list (prod id K)).

Inductive mapsto : list (prod id K) -> id -> K -> Prop :=
  | first : forall (i : id) (k : K) (other : list (prod id K)),
              mapsto ((i, k) :: other) i k
  | next : forall (i i' : id) (k k' : K) (other : list (prod id K)),
              beq_id i i' = false ->
              mapsto other i k ->
              mapsto ((i', k') :: other) i k.

Fixpoint fillhole (small : K) (big : K) :=
  match big with
    | k_hole => small
    | k_list a b => k_list (fillhole small a) (fillhole small b)
    | c_plus a b => c_plus (fillhole small a) (fillhole small b)
    | c_div a b => c_div (fillhole small a) (fillhole small b)
    | c_le a b => c_le (fillhole small a) (fillhole small b)
    | c_not a => c_not (fillhole small a)
    | c_and a b => c_and (fillhole small a) (fillhole small b)
    | c_assignment a b => c_assignment (fillhole small a) (fillhole small b)
    | c_seq a b => c_seq (fillhole small a) (fillhole small b)
    | c_ifthenelse a b c => c_ifthenelse 
                              (fillhole small a) (fillhole small b) (fillhole small c)
    | c_while a b => c_while (fillhole small a) (fillhole small b)
    | c_pgm d a => c_pgm d (fillhole small a)
    | _ => big
  end.

Inductive transition : cfg -> cfg -> Prop :=
  | lookup : forall (X : id) (I : int) (other : K) (map : list (prod id K)),
               mapsto map X (c_int I) ->
               transition (k_list (c_id X) other, map)
                          (k_list (c_int I) other, map)
  | cool : forall (k : K) (other : K) (map : list (prod id K)),
           is_value k = true ->
           transition (k_list k other, map) (fillhole k other, map)
  | heat_nothing : forall (k : K) (m : list (prod id K)),
           transition (k, m) (k_list k k_nothing, m)
  | heat_plus_1 : forall (a1 a2 : K) (other : K) (map : list (prod id K)),
           transition (k_list (c_plus a1 a2) other, map)
                      (k_list a1 (k_list (c_plus k_hole a2) other), map)
  | heat_plus_2 : forall (a1 a2 : K) (other : K) (map : list (prod id K)),
           transition (k_list (c_plus a1 a2) other, map)
                      (k_list a2 (k_list (c_plus a1 k_hole) other), map)
  | add : forall (I1 I2 : int) (a1 a2 : K) (other : K) (map : list (prod id K)),
          a1 = c_int I1 ->
          a2 = c_int I2 ->
          transition (k_list (c_plus a1 a2) other, map)
                     (k_list (c_int (I1 + I2)) other, map).

Inductive rt_closure : (cfg -> cfg -> Prop) -> cfg -> cfg -> Prop :=
  | rt_base : forall (r : cfg -> cfg -> Prop) (c d : cfg),
              r c d ->
              rt_closure r c d
  | rt_refl : forall (r : cfg -> cfg -> Prop) (c : cfg),
              rt_closure r c c
  | rt_trans : forall (r : cfg -> cfg -> Prop) (c d e : cfg),
              rt_closure r c d ->
              rt_closure r d e ->
              rt_closure r c e.

Definition transition_rt := rt_closure transition.

Example test_1 :
  transition_rt (c_plus (c_id (Id 1)) (c_int 10), (Id 1, c_int 20) :: nil)
             (k_list (c_id (Id 1)) (k_list (c_plus k_hole (c_int 10)) k_nothing), (Id 1, c_int 20) :: nil).
Proof.             
  simpl.
  apply rt_trans with (d := (k_list (c_plus (c_id (Id 1)) (c_int 10)) k_nothing,
                            (Id 1, c_int 20) :: nil)).
  apply rt_base.
  apply heat_nothing.
  apply rt_base.
  apply heat_plus_1.
Qed.


Example test_2 :
  transition_rt (k_list (c_id (Id 1)) (k_list (c_plus k_hole (c_int 10)) k_nothing),
                 (Id 1, c_int 20) :: nil)
                (k_list (c_int 20) (k_list (c_plus k_hole (c_int 10)) k_nothing),
                 (Id 1, c_int 20) :: nil).
Proof.             
  simpl.
  apply rt_base.
  apply lookup.
  apply first.
Qed.

Example test_3 :
  transition_rt (k_list (c_int 20) (k_list (c_plus k_hole (c_int 10)) k_nothing),
                 (Id 1, c_int 20) :: nil)
                (k_list (c_plus (c_int 20) (c_int 10)) k_nothing,
                 (Id 1, c_int 20) :: nil).
Proof.             
  simpl.
  apply rt_base.
  replace (k_list (c_plus (c_int 20) (c_int 10)) k_nothing) with (fillhole (c_int 20) (k_list (c_plus k_hole (c_int 10)) k_nothing)).
  apply cool.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Example test_4 :
  transition_rt (k_list (c_plus (c_int 20) (c_int 10)) k_nothing,
                 (Id 1, c_int 20) :: nil)
                (k_list (c_int 30) k_nothing,
                 (Id 1, c_int 20) :: nil).
Proof.             
  simpl.
  apply rt_base.
  replace 30 with (20 + 10).
  apply add.
  reflexivity.
  simpl. reflexivity.
  simpl. reflexivity.
Qed.

Example test_result :
  transition_rt (c_plus (c_id (Id 1)) (c_int 10), (Id 1, c_int 20) :: nil)
                (k_list (c_int 30) k_nothing, (Id 1, c_int 20) :: nil).

eapply rt_trans.
apply test_1.
eapply rt_trans.
apply test_2.
eapply rt_trans.
apply test_3.
eapply rt_trans.
apply test_4.
apply rt_refl.
Qed.

Require Import EqNat.
SearchAbout nat.

Example test_transitive : 
  forall (transition_rt : cfg -> cfg -> Prop) (v : K) (m : list (prod id K)),
    rt_closure transition = transition_rt ->
    is_value v = true ->
    transition_rt (c_plus (c_id (Id 1)) (c_int 10), ((Id 1, c_int 20) :: nil)) (v, m) ->
    v = c_int 30.
Proof.
simpl.
intros.
rewrite <- H in H1.
