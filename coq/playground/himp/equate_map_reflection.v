Require Import domains.
Require Import String.
Require Import List.
Require Import NPeano.

Inductive item_rep : Set :=
  | item (k v : nat)
  | submap (m : nat)
  .
Inductive map_rep : Set :=
  | empty
  | join (l r : map_rep)
  | atom (a : item_rep)
  .

Definition interp_item {K V} keys values submaps (i : item_rep) : Map K V :=
  match i with
    | item k v =>
      match nth_error keys k, nth_error values v with
        | Some k, Some v => k |-> v
        | _, _ => mapEmpty
      end
    | submap m =>
      match nth_error submaps m with
        | Some m => m
        | _ => mapEmpty
      end
  end.

Definition interp {K V} keys values submaps : map_rep -> Map K V :=
  fix eval m := match m with
    | empty => mapEmpty
    | join l r => eval l :* eval r
    | atom a => interp_item keys values submaps a
  end.

Definition mapEq {K V} keys values (submaps : list (Map K V)) ml mr : Prop :=
     interp keys values submaps ml
  ~= interp keys values submaps mr.

Fixpoint merge {A} (lt : A -> A -> bool) (l1 l2 : list A) : list A :=
  match l1 with
    | nil => l2
    | (cons v1 l1') =>
      (fix scan l2 :=
         match l2 with
           | nil => l1
           | cons v2 l2' =>
             if lt v1 v2
             then cons v1 (merge lt l1' l2)
             else cons v2 (scan l2')
         end) l2
  end.

Definition test1 : merge NPeano.ltb (cons 1 (cons 3 (cons 4 nil))) (cons 0 (cons 2 (cons 5 nil)))
                    = cons 0 (cons 1 (cons 2 (cons 3 (cons 4 (cons 5 nil)))))
                           := eq_refl _.


Fixpoint removeMatches' {A} (cmp : A -> A -> comparison) (l1 l2 l1_acc l2_acc : list A) : (list A * list A) :=
  match l1 with
    | nil => (rev l1_acc, rev_append l2_acc l2)
    | (cons v1 l1') =>
      (fix scan l2 l2_acc {struct l2} :=
         match l2 with
           | nil => (rev_append l1_acc l1, rev l2_acc)
           | cons v2 l2' =>
             match cmp v1 v2 with
               | Lt => removeMatches' cmp l1' l2 (v1::l1_acc) l2_acc
               | Eq => removeMatches' cmp l1' l2' l1_acc l2_acc
               | Gt => scan l2' (v2::l2_acc)
             end
         end) l2 l2_acc
  end.

Definition removeMatches {A} cmp (l1 l2 : list A) := removeMatches' cmp l1 l2 nil nil.

Definition test2 :
  removeMatches Nat.compare (cons 1 (cons 3 (cons 4 nil))) (cons 0 (cons 1 (cons 2 (cons 4 nil))))
  = (cons 3 nil, cons 0 (cons 2 nil)) := eq_refl _.

Definition item_lt (i1 i2 : item_rep) : bool :=
  match i1, i2 with
    | item k v, item k2 v2 =>
      orb (ltb k k2) (andb (Nat.eqb k k2) (ltb v v2))
    | item _ _, submap _ => true
    | submap _, item _ _ => false
    | submap m, submap m2 => ltb m m2
  end.
Definition item_cmp (i1 i2 : item_rep) : comparison :=
  match i1, i2 with
    | item k v, item k2 v2 =>
      match Nat.compare k k2 with
        | Eq => Nat.compare v v2
        | o => o
      end
    | item _ _, submap _ => Lt
    | submap _, item _ _ => Gt
    | submap m, submap m2 => Nat.compare m m2
  end.

Lemma item_cmp_prop : forall i1 i2, item_cmp i1 i2 = Eq -> i1 = i2.
Proof.
destruct i1;destruct i2;simpl;unfold Nat.compare;
repeat match goal with [|-context [Compare_dec.nat_compare ?x ?y]] =>
                   destruct (Compare_dec.nat_compare_spec x y) end;
congruence.
Qed.

Definition joins (l : list map_rep) := fold_right join empty l.
Fixpoint canonicalize (m : map_rep) : list item_rep :=
  match m with
    | empty => nil
    | join l r => merge item_lt (canonicalize l) (canonicalize r)
    | atom a => cons a nil
  end.

Section Equivalence.
  Variables K V : Type.
  Variable keys : list K.
  Variable values : list V.
  Variable submaps : list (Map K V).

  Local Notation int := (interp keys values submaps).

  Lemma merge_join {A} (lt : A -> A -> bool) (f : A -> map_rep) (l1 l2 : list A) :
    int (joins (map f (merge lt l1 l2)))
        ~= int (join (joins (map f l1)) (joins (map f l2))).

  revert l2; induction l1; intro; simpl.
  rewrite equivUnitL; reflexivity.
  induction l2; simpl.
  rewrite equivUnit; reflexivity.
  destruct (lt a a0); simpl.
  rewrite IHl1; simpl; equate_maps.
  rewrite IHl2; equate_maps.
  Qed.

  Lemma canon_equiv : forall m, int m ~= int (joins (map atom (canonicalize m))).
  Proof.
    induction m;simpl;rewrite ?equivUnit, ?equivUnitL; try reflexivity.
    rewrite IHm1, IHm2, merge_join. reflexivity.
  Qed.

  Lemma app_equiv l1 l2 : int (joins (l1 ++ l2)) ~= int (joins l1) :* int (joins l2).
    induction l1.
    simpl; rewrite equivUnitL; reflexivity.
    simpl; rewrite IHl1, equivAssoc; reflexivity.
  Qed.

  Section RemoveEquiv.
    Variable m1 m2 : map_rep. (* Need a rest of map to make this flexible enough *)

  Local Notation build_equiv l1 l2 := (int (joins (m1 :: map atom l1)) ~= int (joins (m2 :: map atom l2))).

  Lemma removeEquivSubmaps (l1 l2 l1_acc l2_acc : list item_rep) :
    match removeMatches' item_cmp l1 l2 l1_acc l2_acc with
      | (l1', l2') => build_equiv l1' l2'
    end ->
    build_equiv (rev_append l1_acc l1) (rev_append l2_acc l2).
  revert l1_acc l2 l2_acc;induction l1.
  simpl; intros; rewrite <- rev_alt; assumption.
  induction l2.
  simpl; intros; rewrite <- rev_alt; assumption.
  intros; simpl in * |- *.
  destruct (item_cmp a a0) eqn:Hcmp.
  (* Both step? *)
  Focus 3.
  (* Gt -> use inner IH *)
  apply (IHl2 (a0 :: l2_acc)).
  apply H.
  (* Eq -> goes back to outer IH, with thing dropped *)
  specialize (IHl1 _ _ _ H); clear -Hcmp IHl1.
    (* rearranging. *)
    apply item_cmp_prop in Hcmp. subst a.
    rewrite !rev_append_rev, !map_app, !app_equiv in IHl1 |- *.
    simpl.
    repeat rewrite (equivComAssoc _ (interp_item _ _ _ a0) _).
    rewrite IHl1. reflexivity.
  (* Lt -> use outer IH? *)  
  apply IHl1 with (l1_acc := (a :: l1_acc)).
  assumption.
  Qed.
  End RemoveEquiv.

  Lemma reduce_equiv (rep1 rep2 : map_rep) :
    match removeMatches item_cmp (canonicalize rep1) (canonicalize rep2) with
      | (items1, items2) =>
        int (joins (map atom items1)) ~= int (joins (map atom items2))
    end
    -> int rep1 ~= int rep2.
  Proof.
    unfold removeMatches; intros.
    rewrite (canon_equiv rep1), (canon_equiv rep2).
    setoid_rewrite <- equivUnitL.
    change (int (joins (empty :: map atom (rev_append nil (canonicalize rep1))))
         ~= int (joins (empty :: map atom (rev_append nil (canonicalize rep2))))).
    apply removeEquivSubmaps.
    destruct (removeMatches' item_cmp (canonicalize rep1) 
         (canonicalize rep2) nil nil).
    simpl; rewrite H; reflexivity.
  Qed.
End Equivalence.

Definition test3 : forall (k1 k2 : string) (v1 v2 : nat) (m1 : Map string nat),
                     k1 |-> v1 :* m1 :* k2 |-> v2 ~= m1 :* k2 |-> v2 :* k1 |-> v1.
Proof.
intros.
change
  (interp (k1 :: k2 :: nil) (v1 :: v2 ::nil) (m1 :: nil)
        (join (atom (item 0 0)) (join (atom (submap 0)) (atom (item 1 1))))
     ~= 
  interp (k1 :: k2 :: nil) (v1 :: v2 ::nil) (m1 :: nil)
        (join (atom (submap 0)) (join (atom (item 1 1)) (atom (item 0 0))))).
apply reduce_equiv.
simpl.
reflexivity.
Qed.

Ltac inList x xs :=
  match xs with
      | nil => false
      | x :: _ => true
      | _ :: ?xs' => inList x xs'
  end.
Ltac insert x xs :=
  match inList x xs with
    | true => xs
    | false => constr:(x :: xs)
  end.
Ltac index x xs :=
  match xs with
    | (x :: _) => constr:0
    | (?x' :: ?xs) => let ix := index x xs in constr:(S ix)
  end.
Ltac gatherKeys gathered t :=
  match t with
    | ?l :* ?r => let gathered' := gatherKeys gathered l in gatherKeys gathered' r
    | (?k |-> _) => insert k gathered
    | _ => gathered
  end.
Ltac gatherValues gathered t :=
  match t with
    | ?l :* ?r => let gathered' := gatherValues gathered l in gatherValues gathered' r
    | (_ |-> ?v) => insert v gathered
    | _ => gathered
  end.
Ltac gatherSubmaps gathered t :=
  match t with
    | ?l :* ?r => let gathered' := gatherSubmaps gathered l in gatherSubmaps gathered' r
    | (_ |-> ?v) => gathered
    | ?m => insert m gathered
  end.

Ltac quoteMap ks vs ms t :=
  match t with
    | (@mapEmpty _ _) => empty
    | ?l :* ?r =>
      let repl := quoteMap ks vs ms l in
      let repr := quoteMap ks vs ms r in
      constr:(join repl repr)
    | ?k |-> ?v =>
      let repk := index k ks in
      let repv := index v vs in
      constr:(atom (item repk repv))
    | ?m =>
      let repm := index m ms in
      constr:(atom (submap repm))
  end.
Ltac quote_map_equation := match goal with
    [|- @MapEquiv ?K ?V ?l ?r ] =>
    let ks := gatherKeys (@nil K) l in
    let ks := gatherKeys ks r in
    let vs := gatherValues (@nil V) l in
    let vs := gatherValues vs r in
    let ms := gatherSubmaps (@nil (Map K V)) l in
    let ms := gatherSubmaps ms r in
    let repl := quoteMap ks vs ms l in
    let repr := quoteMap ks vs ms r in
    change (interp ks vs ms repl ~= interp ks vs ms repr)
end.

Definition test4 : forall (k1 k2 : string) (v1 v2 : nat) (m1 : Map string nat),
                     k1 |-> v1 :* m1 :* k2 |-> v2 ~= m1 :* k2 |-> v2 :* k1 |-> v1.
Proof.
intros.
quote_map_equation.
apply reduce_equiv.
simpl.
reflexivity.
Qed.

Ltac map_simpl := quote_map_equation;apply reduce_equiv;simpl.

Require Import kstyle.
Require Import ZArith.
Coercion EVar : string >-> Exp.
Coercion ECon : Z >-> Exp.

Ltac name_evars t :=
  match t with
    | ?l ~= ?r => name_evars l; name_evars r
    | ?l :* ?r => name_evars l; name_evars r
    | ?k |-> ?v => name_evars k; name_evars v
    | ?m => try (is_evar m;set m)
  end.


