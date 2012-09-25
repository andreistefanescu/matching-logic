(* make terms, experiment with lifting properness from domains to corresponding labels *)
Require Import Setoid.
Require Import Morphisms.
Require Import List.
Require Import Program.

Set Implicit Arguments.

Module Type Labels.
  Parameter sort : Set.
  Parameter domain : sort -> Set.
  Parameter domain_eq : forall s, relation (domain s).
  Parameter domain_eq_equiv : forall s, Equivalence (@domain_eq s).
  Parameter var : sort -> Set.
End Labels.

Fixpoint funty {U : Set} (el : U -> Set) (args : list U) (res : U) : Set :=
  match args with
    | nil => el res
    | (a :: args') => el a -> funty el args' res
  end.

Definition funty' {U : Set} (el el' : U -> Set) (args : list U) (res : U) : Set :=
  @fold_right Set U (fun a r => el a -> r) (el' res) args.

Module Terms (Import labels : Labels).
 
Definition label_ty args res := funty' domain (fun s => option (domain s)) args res.
Inductive Term : forall s : sort, Set :=
 | TVar : forall {s}, var s -> Term s
 | TCon : forall {s args}, label_ty args s-> TArgs args -> Term s
with TArgs : forall (args : list sort), Set :=
 | TNil : TArgs nil
 | TCons : forall {a args}, Term a -> TArgs args -> TArgs (a :: args)
 .

Fixpoint gather {args : list sort} {res : sort} {struct args} :=
  match args as args return (TArgs args -> Term res) -> funty Term args res with
    | nil => fun k => k TNil
    | (cons x xs) => fun k => fun x' => @gather xs _ (fun xs' => k (TCons x' xs'))
  end.

Definition label (args : list sort) (res : sort) (f : label_ty args res) : funty Term args res :=
  gather (TCon f).

Notation Env := (forall s, var s -> option (domain s)).

Fixpoint eval (env : Env) {s} (t : Term s) : option (domain s) :=
  match t with
    | TVar _ v => env _ v
    | TCon _ _ f args => apply env (Some f) args
  end
with apply (env : Env) {args : list sort} {res : sort} (mf : option (label_ty args res))
           (ts : TArgs args){struct ts}  : option (domain res) :=
  match mf with
    | None => None
    | Some f =>
      match ts in TArgs args return label_ty args res -> option (domain res) with
        | TNil => fun f => f
        | TCons _ args' t ts => fun f' =>
          match  eval env t with
            | None => None
            | Some v => apply env (Some (f' v)) ts
          end
      end f
  end.

Definition option_rel (A : Set) (R : relation A) : relation (option A) :=
  fun x y => match x, y with
                | Some v, Some w => R v w
                | None, None => True
                | _, _ => False
              end.

Definition valid (s : sort) : relation (Term s) :=
  fun t1 t2 => forall env,
                 option_rel (@domain_eq s) (eval env t1) (eval env t2).

Fixpoint valid_args (args : list sort) (ts1 : TArgs args) : TArgs args -> Prop :=
  match ts1 in TArgs args' return TArgs args' -> Prop with
    | TNil => fun ts2 => match ts2 with
                             | TNil => True
                             | _ => False
                         end
    | TCons s ss t1 ts1' => fun ts2 =>
      match ts2 in TArgs args'' return match args'' with
                                         | nil => True 
                                         | (s :: ss) => Term s -> TArgs ss -> Prop
                                       end with
          | TNil => I
          | TCons _ _ t2 ts2' => fun t1' ts1'' =>
                                   valid t1' t2 /\ valid_args ts1'' ts2'
      end t1 ts1'
  end.

Lemma valid_refl (s : sort) : Reflexive (@valid s).
intro x; unfold valid. intros. destruct (eval env x); simpl; reflexivity.
Qed.
Lemma valid_trans (s : sort) : Transitive (@valid s).
intro x; unfold valid. intros. specialize (H env).  specialize (H0 env).
destruct (eval env x);destruct (eval env y);simpl in H;try tauto;destruct (eval env z);simpl in H0; try tauto.
simpl. etransitivity;eassumption. 
Qed.

Add Parametric Relation (s : sort) : (Term s) (@valid s)
  reflexivity proved by (@valid_refl s)
  transitivity proved by (@valid_trans s)
  as valid_rel.

Ltac dep_dest_1 := let x := fresh "x" in intro x; dependent destruction x.
Ltac straightforward_reflexivity := dep_dest_1; simpl; intuition reflexivity.
Ltac straightforward_transitivity := do 3 dep_dest_1; simpl; intuition (etransitivity; eassumption).

Lemma valid_args_refl (ss : list sort) : Reflexive (@valid_args ss).
induction ss; straightforward_reflexivity.
Qed.
Lemma valid_args_trans (ss : list sort) : Transitive (@valid_args ss).
induction ss; straightforward_transitivity.
Qed.

Add Parametric Relation (ss : list sort) : (TArgs ss) (@valid_args ss)
  reflexivity proved by (@valid_args_refl ss)
  transitivity proved by (@valid_args_trans ss)
  as valid_args_rel.

Add Parametric Morphism (s : sort) (ss : list sort) : (@TCons s ss)
with signature (@valid s) ++> (@valid_args ss) ++> (@valid_args (s :: ss))
as tcons_valid.
simpl; auto.
Qed.

Fixpoint label_rel args res {struct args} : relation (label_ty args res) :=
  match args as args return relation (label_ty args res) with
    | nil => option_rel (@domain_eq res)
    | a :: args' => (@domain_eq a ++> label_rel args' res)%signature
   end.

Lemma apply_rel
  (args : list sort)
  (res : sort)
  (x : label_ty args res)
  (y : label_ty args res)
  (H : label_rel args res x y)
  (x0 : TArgs args)
  (y0 : TArgs args)
  (H0 : valid_args x0 y0) :
  forall env : Env,
   option_rel (domain_eq (s:=res)) (apply env (Some x) x0)
     (apply env (Some y) y0).
Proof.
intro env.
induction args; dependent destruction x0; dependent destruction y0.
exact H.
destruct H0.
specialize (H0 env).
simpl.
destruct (eval env t);
destruct (eval env t0);
simpl in H0 |- *; try tauto.
simpl in H.
intuition.
Qed.

Add Parametric Morphism (args : list sort) (res : sort) : (@TCon res args)
  with signature (label_rel args res) ++> (@valid_args args) ++> (@valid res)
  as tcon_valid.
Proof.
intros; unfold valid; apply apply_rel; assumption.
Qed.

End Terms.

Module ExpLabel <: Labels.
  Inductive sortI : Set := nsort.
  Definition sort := sortI.
  Definition domain s :=
    match s with
        nsort => nat
    end.
  Definition domain_eq s := @eq (domain s).
  Definition domain_eq_equiv s := @eq_equivalence (domain s).
  Definition var s := option (domain s).
End ExpLabel.

Import ExpLabel.
Module Import lterms := Terms ExpLabel.

Definition oplus : label_ty (nsort :: nsort :: []) nsort  := fun x y => Some (x + y).

Instance plus_proper : Proper (label_rel (nsort :: nsort :: []) nsort) oplus.
repeat (intro; intros).
simpl in * |- *.
unfold domain_eq in * |- *.
congruence.
Qed.

Definition ocon (n : nat) : label_ty [] nsort := Some n.

Instance con_proper (n : nat) : Proper (label_rel [] nsort) (ocon n).
reflexivity.
Qed.

Notation tcon n := (TCon (ocon n) TNil).
Notation tplus l r := (TCon oplus (TCons l (TCons r TNil))).

Lemma computing (x y : nat) : valid (tplus (tcon x) (tcon y)) (tcon (x + y)).
Proof.
unfold valid; reflexivity.
Qed.
Lemma computing_r (x y : nat) : (Basics.flip (@valid _)) (tplus (tcon x) (tcon y)) (tcon (x + y)).
Proof.
unfold flip, valid; reflexivity.
Qed.

Lemma con_equiv (x y : nat) : x = y -> valid (tcon x) (tcon y).
congruence.
Qed.

Instance valid_default (s : sort) : DefaultRelation (@valid s).

Require Import Omega.

Lemma use_computing (x y z w : nat) :
  valid (tplus (tplus (tcon x) (tcon y)) (tplus (tcon z) (tcon w)))
        (tplus (tcon x) (tplus (tplus (tcon y) (tcon z)) (tcon w))).
Proof.
do 3 rewrite computing.
do 3 rewrite computing_r.
apply con_equiv.
omega.
Qed.