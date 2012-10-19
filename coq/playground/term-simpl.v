(* make terms, experiment with lifting properness from domains to corresponding labels *)
Require Import Setoid.
Require Import Morphisms.
Require Import List.
Require Import Program.

Set Implicit Arguments.

Generalizable All Variables.

Definition funty `(el : U -> Type) args res :=
  fold_right  (fun a r => el a -> r) (el res) args.

Definition funrel `(rels : forall (u : U), relation (el u))
           args res : relation (funty el args res) :=
 list_rect (fun args => relation (funty el args res))
           (rels res) (fun a _ rs => respectful (rels a) rs) args.

Definition funty' `(el : U -> Type) args res :=
  fold_right  (fun a r => el a -> r) (option (el res)) args.

Definition option_impl `(R : relation A) : relation (option A) :=
  fun x y => match x, y with
                | Some v, Some w => R v w
                | None, _ => True
                | _, _ => False
              end.

Definition funrel' `(rels : forall (u : U), relation (el u))
           args res : relation (funty' el args res) :=
 list_rect (fun args => relation (funty' el args res))
           (option_impl (rels res)) (fun a _ rs => respectful (rels a) rs) args.

Module Type Labels.
  Parameter sort : Set.
  Parameter domain : sort -> Set.
  Parameter domain_eq : forall s, relation (domain s).
  Parameter domain_eq_equiv : forall s, Equivalence (@domain_eq s).
  Parameter label : Set.
  Parameter label_args : label -> list sort.
  Parameter label_res : label -> sort.
  Parameter label_sem : forall l, funty' domain (label_args l) (label_res l).
  Parameter label_proper : forall l, Proper (funrel' domain_eq (label_args l) (label_res l)) (label_sem l).
  Parameter var : sort -> Set.
End Labels.

Module Terms (Import labels : Labels).

Definition label_ty args res := funty' domain args res.

Unset Implicit Arguments.
Inductive Term : forall s : sort, Type :=
 | TVar : forall {s}, var s -> Term s
 | TCon : forall l, TArgs (label_args l) -> Term (label_res l)
with TArgs : forall (args : list sort), Type :=
 | TNil : TArgs nil
 | TCons : forall {a args}, Term a -> TArgs args -> TArgs (a :: args)
 .
Set Implicit Arguments.

Fixpoint gather {args : list sort} {res : sort} {struct args} :=
  match args as args return (TArgs args -> Term res) -> funty Term args res with
    | nil => fun k => k TNil
    | (cons x xs) => fun k => fun x' => @gather xs _ (fun xs' => k (TCons x' xs'))
  end.

Definition lapply (l : label) := gather (TCon l).

Notation Env := (forall s, var s -> option (domain s)).

Fixpoint eval (env : Env) {s} (t : Term s) : option (domain s) :=
  match t with
    | TVar _ v => env _ v
    | TCon f args => apply env (Some (label_sem f)) args
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

Definition valid_impl (s : sort) : relation (Term s) :=
  fun t1 t2 => forall env,
                 option_impl (@domain_eq s) (eval env t1) (eval env t2).

Lemma valid_impl_refl (s : sort) : Reflexive (@valid_impl s).
intro x; unfold valid_impl. intros. destruct (eval env x); simpl; reflexivity.
Qed.
Lemma valid_impl_trans (s : sort) : Transitive (@valid_impl s).
intro x; unfold valid_impl. intros. specialize (H env).  specialize (H0 env).
destruct (eval env x);destruct (eval env y);simpl in H;try tauto;destruct (eval env z);simpl in H0; try tauto.
simpl. etransitivity;eassumption. 
Qed.

Add Parametric Relation (s : sort) : (Term s) (@valid_impl s)
  reflexivity proved by (@valid_impl_refl s)
  transitivity proved by (@valid_impl_trans s)
  as valid_rel.

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
                                   valid_impl t1' t2 /\ valid_args ts1'' ts2'
      end t1 ts1'
  end.


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
with signature (@valid_impl s) ++> (@valid_args ss) ++> (@valid_args (s :: ss))
as tcons_valid.
simpl; auto.
Qed.

Lemma apply_rel
  (args : list sort)
  (res : sort)
  (x : funty' domain args res)
  (y : funty' domain args res)
  (H : funrel' domain_eq args res x y)
  (x0 : TArgs args)
  (y0 : TArgs args)
  (H0 : valid_args x0 y0) :
  forall env : Env,
   option_impl (domain_eq (s:=res)) (apply env (Some x) x0)
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
apply IHargs; auto.
Qed.

Add Parametric Morphism l : (TCon l)
  with signature (@valid_args (label_args l)) ++> (@valid_impl (label_res l))
  as tcon_valid.
Proof.
intros; unfold valid_impl; apply apply_rel; [apply label_proper |  assumption].
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

  Inductive labelI : Set :=
    | lplus
    | lcon (n : nat).
  Definition label := labelI.
  Definition label_args (l : labelI) :=
    match l with
      | lplus => [nsort ; nsort]
      | lcon _ => nil
    end.
  Definition label_res (l : labelI) := nsort.
  Definition label_sem (l : labelI) :=
    match l as l return funty' domain (label_args l) (label_res l) with
      | lplus => fun x y => Some (x + y)
      | lcon v => Some v
    end.
  Definition label_proper (l : labelI) : Proper (funrel' domain_eq (label_args l) (label_res l)) (label_sem l).
    destruct l; unfold Proper; simpl; unfold domain_eq, respectful; congruence.
  Qed.
End ExpLabel.

Import ExpLabel.
Module Import lterms := Terms ExpLabel.

Notation tcon n := (TCon (lcon n) TNil : Term nsort).
Notation tplus l r := (TCon lplus (TCons l (TCons r TNil)) : Term nsort).

Lemma computing (x y : nat) : valid_impl (tplus (tcon x) (tcon y)) (tcon (x + y)).
Proof.
unfold valid_impl; reflexivity.
Qed.
Check computing.

Lemma computing_r (x y : nat) : (Basics.flip (@valid_impl _)) (tplus (tcon x) (tcon y)) (tcon (x + y)).
Proof.
unfold flip, valid_impl; reflexivity.
Qed.

Lemma con_equiv (x y : nat) : x = y -> valid_impl (tcon x) (tcon y).
congruence.
Qed.

Instance valid_default (s : sort) : DefaultRelation (@valid_impl s).
Instance valids_default (ss : list sort) : DefaultRelation (@valid_args s).

Fixpoint bu (simpl : forall s, Term s -> Term s) s (t : Term s) : Term s :=
  match t in Term s' return Term s' with
    | (TVar _ _ as t') => simpl _ t'
    | TCon l args => simpl _ (TCon l (bus simpl args))
  end
with bus (simpl : forall s, Term s -> Term s) ss (ts : TArgs ss) : TArgs ss :=
  match ts in TArgs ss' return TArgs ss' with
    | TNil => TNil
    | TCons _ _ t ts' => TCons (bu simpl t) (bus simpl ts')
  end.

Lemma bu_simpls : forall (simpl : forall s, Term s -> Term s)
      (simpl_simpls : forall s (t : Term s), valid_impl t (simpl s t)),
      forall s (t : Term s), valid_impl t (bu simpl t)
with bus_simpls : forall (simpl : forall s, Term s -> Term s)
      (simpl_simpls : forall s (t : Term s), valid_impl t (simpl s t)),
      forall ss (ts : TArgs ss), valid_args ts (bus simpl ts).
Proof.
clear bu_simpls. destruct t;simpl;auto.
rewrite <- simpl_simpls.
auto using tcon_valid.

clear bus_simpls. induction ts;simpl;auto.
Qed.

Definition simpl_plus s : Term s -> Term s :=
 match s as s return Term s -> Term s with
   | nsort => fun t => match t with
                         | TCon lplus (TCons _ _ (TCon (lcon x) TNil)
                                             (TCons _ _ (TCon (lcon y) TNil)
                                                    TNil)) => TCon (lcon (x + y)) TNil
                         | _ => t
                       end
 end.

Lemma simpl_plus_simpls : forall s (t : Term s), valid_impl t (simpl_plus t).
intros.
destruct t.
destruct s. reflexivity.
destruct l; try reflexivity.
dependent destruction t.
dependent destruction t1.
fold sort in t1.
dependent destruction t1.
dependent destruction t.
reflexivity.
destruct l.
reflexivity.
simpl in t.
dependent destruction t.
dependent destruction t2.
reflexivity.
destruct l.
reflexivity.
simpl in t.
dependent destruction t.
simpl.
unfold valid_impl.
simpl.
reflexivity.
Qed.

Require Import Omega.

Lemma test_computing (x y z : nat) :
  valid_impl (tplus (tplus (tcon x) (tcon y)) (tcon z))
             (tcon ((x + y) + z)).
autounfold.
rewrite computing.
autounfold.
rewrite computing.

pose proof (computing (x + y) z).
Set Printing All.
autounfold.
autounfold in H.
rewrite H.
Check trans_co_eq_inv_impl_morphism.
Check
(tcons_valid_Proper (computing x y) (TCons (tcon z) TNil) 
          (TCons (tcon z) TNil)
          (reflexive_proper_proxy
             (valid_args_rel_Reflexive (ss:=[label_res (lcon z)]))
             (TCons (tcon z) TNil)))
.
test_computing = 
(fun
   H : valid_impl (tplus (tcon (x + y)) (tcon z))
         (tplus (tcon (x + y)) (tcon z)) =>
 (fun lemma : valid_impl (tplus (tcon x) (tcon y)) (tcon (x + y)) =>
  trans_co_eq_inv_impl_morphism (valid_rel_Transitive (s:=label_res lplus))
    (tplus (tplus (tcon x) (tcon y)) (tcon z))
    (tplus (tcon (x + y)) (tcon z))
    (tcon_valid_Proper
       (TCons (tplus (tcon x) (tcon y)) (TCons (tcon z) TNil))
       (TCons (tcon (x + y)) (TCons (tcon z) TNil))
       (tcons_valid_Proper lemma (TCons (tcon z) TNil) 
          (TCons (tcon z) TNil)
          (reflexive_proper_proxy
             (valid_args_rel_Reflexive (ss:=[label_res (lcon z)]))
             (TCons (tcon z) TNil)))) (tplus (tcon (x + y)) (tcon z))
    (tplus (tcon (x + y)) (tcon z))
    (eq_proper_proxy (Term (label_res lplus)) (tplus (tcon (x + y)) (tcon z))))
   (computing x y) H) (reflexivity (tplus (tcon (x + y)) (tcon z)))
     : forall x y z : nat,
       valid_impl (tplus (tplus (tcon x) (tcon y)) (tcon z))
         (tplus (tcon (x + y)) (tcon z))


rewrite computing.
reflexivity.
Qed.
Print test_computing.



Lemma use_computing (x y z w : nat) :
  valid_impl (tplus (tplus (tcon x) (tcon y)) (tplus (tcon z) (tcon w)))
             (tplus (tcon x) (tplus (tplus (tcon y) (tcon z)) (tcon w))).
Proof.
assert 
cut (valid_impl (tcon ((x + y) + (z + w)))
                (tplus (tcon x) (tplus (tplus (tcon y) (tcon z)) (tcon w)))).
rewrite computing.
assert (Proper (valid_impl (s:=label_res lplus) ==> flip (@valid_impl (label_res lplus)) ==> flip impl)
               (valid_impl (s:=label_res lplus))).
unfold Proper.
unfold flip.
intro. intros.
intro. intros.
intro.
transitivity y0. assumption.
transitivity y1. assumption.
assumption.

Lemma 
rewrite computing.
rewrite computing.
setoid_rewrite computing.

rewrite (bu_simpls _ simpl_plus_simpls).
simpl.
congruence omega.
setoid_rewrite computing.
repeat match goal with [|- valid ?pre _] =>
       match pre with context [tplus (tcon ?l) (tcon ?r)] => rewrite (computing l r) end end.
repeat match goal with [|- valid _ ?post] =>
       match post with context [tplus (tcon ?l) (tcon ?r)] => rewrite (computing_r l r) end end.
apply con_equiv.
omega.
Qed.

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