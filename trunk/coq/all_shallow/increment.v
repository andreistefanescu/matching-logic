Require Import List.

Inductive k :=
  | Con (n : nat)
  | Suc (v : k)
  | Store (val : k)
  | Load
  | Hole
  .

Inductive cfg := Cfg (pgm1 pgm2 : list k) (val : nat).

Definition is_value k :=
  match k with
    | Con _ => true
    | _ => false
  end.

Inductive istep : list k -> nat -> list k -> nat -> Prop :=
  (* computation *)
  | e_suc : forall n r s, istep (Suc (Con n) :: r) s (Con (S n) :: r) s
  | e_store : forall n r v, istep (Store (Con n) :: r) v r n
  | e_load : forall r v, istep (Load :: r) v (Con v :: r) v
  (* focusing *)
  | h_suc : forall k r v, is_value k = false -> istep (Suc k :: r) v (k :: Suc Hole :: r) v
  | c_suc : forall n r v, istep (Con n :: Suc Hole :: r) v (Suc (Con n) :: r) v
  | h_store : forall k r v, is_value k = false -> istep (Store k :: r) v (k :: Store Hole :: r) v
  | c_store : forall n r v, istep (Con n :: Store Hole :: r) v (Store (Con n) :: r) v
  .
                            
Inductive step : cfg -> cfg -> Prop :=
| left_step : forall pgm1 pgm1' env env', istep pgm1 env pgm1' env' -> forall pgm2,
     step (Cfg pgm1 pgm2 env) (Cfg pgm1' pgm2 env')
| right_step : forall pgm2 pgm2' env env', istep pgm2 env pgm2' env' -> forall pgm1,
     step (Cfg pgm1 pgm2 env) (Cfg pgm1 pgm2' env')
.

CoInductive allreach (gamma : cfg) (phi : cfg -> Prop) : Prop :=
  | reach_here : phi gamma -> allreach gamma phi
  | reach_next : (exists gamma', step gamma gamma') ->
                 (forall gamma', step gamma gamma' ->
                                 allreach gamma' phi) ->
                 allreach gamma phi.

Definition goal c :=
  match c with
    | Cfg nil nil n => n = 1 \/ n = 2
    | _ => False
  end.

(* trace is 
 Store (Suc Load)
 Suc Load :: Store Hole
 Load :: Suc Hole :: Store Hole
 then splits into
 Con n :: Suc Hole :: Store Hole
 with n = 0 \/ n = 1
 Suc (Con n) :: Store Hole
 Con (S n) :: Store Hole
 Store (S n)
*)



Definition before_load pgm :=
 In pgm ((Store (Suc Load) :: nil)
           :: (Suc Load :: Store Hole :: nil)
           :: (Load :: Suc Hole :: Store Hole :: nil)
           :: nil).
Definition after_load n pgm :=
  In pgm ((Con n :: Suc Hole :: Store Hole :: nil)
            :: (Suc (Con n) :: Store Hole :: nil)
            :: (Con (S n) :: Store Hole :: nil)
            :: (Store (Con (S n)) :: nil)
            :: nil).
(*
           0
         1   2
       3   4   5
       |  7 8  |
       6  11  9
        \    /
          10
*)
Definition cbefore pgm :=
  match pgm with
    | Store (Suc Load) :: nil => True
    | Suc Load :: Store Hole :: nil => True
    | Load :: Suc Hole :: Store Hole :: nil => True
    | _ => False
  end.
Lemma cbefore_before : forall p, cbefore p -> before_load p.
unfold cbefore.
intro p;
repeat match goal with
| [|- match ?p with nil => _ | _ => _ end -> _] => destruct p; try tauto
| [|- match ?k with Hole => _ | _ => _ end -> _] => destruct k; try tauto
end;
unfold before_load;simpl;tauto.
Qed.

Definition cafter k pgm :=
  match pgm with
    | (Con n :: Suc Hole :: Store Hole :: nil) => k = n
    | (Suc (Con n) :: Store Hole :: nil) => k = n
    | (Con (S n) :: Store Hole :: nil) => k = n
    | (Store (Con (S n)) :: nil) => k = n
    | _ => False
  end.
Lemma cafter_after : forall k p, cafter k p -> after_load k p.
unfold cafter.
intros k p.
repeat match goal with
| [|- match ?p with nil => _ | _ => _ end -> _] => destruct p; try tauto
| [|- match ?k with Hole => _ | _ => _ end -> _] => destruct k; try tauto
| [|- match ?k with O => _ | _ => _ end -> _] => destruct k; try tauto
end;
unfold after_load;simpl;intro;subst;tauto.
Qed.
                                         
Definition states pgm1 pgm2 n :=
     (before_load pgm1 /\ before_load pgm2 /\ n = 0)   (* 0 -> 1 | 2*)
  \/ (after_load 0 pgm1 /\ before_load pgm2 /\ n = 0)  (* 1 -> 3 | 4 *)
  \/ (before_load pgm1 /\ after_load 0 pgm2 /\  n = 0) (* 2 -> 4 | 5 *)
  \/ (pgm1 = nil /\ before_load pgm2 /\ n = 1)         (* 3 -> . | 6 *)
  \/ (after_load 0 pgm1 /\ after_load 0 pgm2 /\ n = 0) (* 4 -> 7 | 8 *)
  \/ (before_load pgm1 /\ pgm2 = nil /\  n = 1)        (* 5 -> 9 | . *)
  \/ (pgm1 = nil /\ after_load 1 pgm2 /\ n = 1)        (* 6 -> . | 10 *)
  \/ (pgm1 = nil /\ after_load 0 pgm2 /\ n = 1)        (* 7 -> . | 11 *)
  \/ (after_load 0 pgm1 /\ pgm2 = nil /\ n = 1)        (* 8 *)
  \/ (after_load 1 pgm1 /\ pgm2 = nil /\  n = 1)       (* 9 *)
  \/ (pgm1 = nil /\ pgm2 = nil /\ n = 2)               (* 10 *)
  \/ (pgm1 = nil /\ pgm2 = nil /\ n = 1)               (* 11 *)
   .

Definition cstates (pgm1 pgm2 : list k) n :=
  match pgm1, pgm2 with
    | nil, nil => n = 1 \/ n = 2
    | nil, _ => n = 1 /\ (cbefore pgm2 \/ cafter 0 pgm2 \/ cafter 1 pgm2)
    | _, nil => n = 1 /\ (cbefore pgm1 \/ cafter 0 pgm1 \/ cafter 1 pgm1)
    | _, _ => n = 0 /\ (cbefore pgm1 \/ cafter 0 pgm1) /\ (cbefore pgm2 \/ cafter 0 pgm2)
  end.
Lemma cstates_states : forall p1 p2 n, cstates p1 p2 n -> states p1 p2 n.                       
unfold cstates.
intros p1 p2 n.
pose proof (cbefore_before p1).
pose proof (cbefore_before p2).
pose proof (cafter_after 0 p1).
pose proof (cafter_after 1 p1).
pose proof (cafter_after 0 p2).
pose proof (cafter_after 1 p2).
destruct p1; destruct p2; unfold states;tauto.
Qed.

Inductive Delay (P : Prop) : Prop := delay (p : P).

CoFixpoint increments :
  forall p1 p2 n, states p1 p2 n -> allreach (Cfg p1 p2 n) goal.
apply delay in increments.
unfold states, before_load, after_load, In; intuition; subst;
match goal with
  | [|- allreach (Cfg nil nil _) goal ] => solve[apply reach_here;simpl;auto]
  | [|- allreach (Cfg _ _ _) goal ] =>
           apply reach_next;[eexists;econstructor(econstructor (reflexivity))|]
end;
intros;
match goal with
  | [ H : step _ _ |- _] => inversion H;subst;clear H
end;
match goal with
  | [ H' : istep _ _ _ _ |- _] => inversion H';subst;apply increments;apply cstates_states;simpl;tauto
end.
Qed.