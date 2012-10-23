Require Import BinPos.
Require Import ZArith.
Require Import FMapPositive.
Require Import String.

Require Import Setoid.

Set Implicit Arguments.

Inductive Map (Key Elt : Type) : Type :=
| mapEmpty
| mapItem (k : Key) (v : Elt)
| mapJoin (m1 m2 : Map Key Elt)
.
Arguments mapEmpty [Key Elt].

Infix ":->" := mapItem (at level 50, no associativity).
Infix ":*" := mapJoin (at level 60, right associativity).

Inductive MapEquiv {K E : Type} : Map K E -> Map K E -> Prop :=
| equivUnit : forall m, MapEquiv (m :* mapEmpty) m
| equivComm : forall m1 m2, MapEquiv (m1 :* m2) (m2 :* m1)
| equivAssoc : forall m1 m2 m3, MapEquiv ((m1 :* m2) :* m3) (m1 :* (m2 :* m3))

| equivJoin : forall l1 r1 l2 r2, MapEquiv l1 l2 -> MapEquiv r1 r2 -> MapEquiv (l1 :* r1) (l2 :* r2)
| equivTrans : forall m1 m2 m3, MapEquiv m1 m2 -> MapEquiv m2 m3 -> MapEquiv m1 m3
| equivSym : forall m1 m2, MapEquiv m1 m2 -> MapEquiv m2 m1
| equivRefl : forall m, MapEquiv m m
.
Infix "~=" := MapEquiv (at level 70, no associativity).

Definition equivJoinL {K V} (r : Map K V) l1 l2 pfl : l1 :* r ~= l2 :* r :=
  equivJoin pfl (equivRefl r).
Definition equivJoinR {K V} (l : Map K V) r1 r2 pfr :  l :* r1 ~= l :* r2 :=
  equivJoin (equivRefl l) pfr.

Add Parametric Relation (K E : Type) : (Map K E) MapEquiv
  reflexivity proved by equivRefl                        
  symmetry proved by equivSym
  transitivity proved by equivTrans
  as map_equiv_rel.

Add Parametric Morphism K E : (@mapJoin K E) with
  signature MapEquiv ==> MapEquiv ==> MapEquiv as map_join_mor.
Proof. auto using equivJoin. Qed.

Lemma mapComAssoc : forall {K V} (m1 m2 m3 : Map K V), m1 :* m2 :* m3 ~= m2 :* m1 :* m3.
intros. rewrite <- equivAssoc, (equivComm m1 m2), equivAssoc. reflexivity. Qed.

(* Language syntax *)
Inductive Exp :=
  | EVar (v:string)
  | ECon (i:Z)
  | EPlus (l r:Exp)
  | EMinus (l r:Exp)
  | EDiv (l r:Exp)
  .
Definition isEVal e :=
  match e with
    | ECon _ => true
    | _ => false
  end.
Inductive BExp :=
  | BCon (b:bool)
  | BLe (l r : Exp)
  | BNot (e:BExp)
  | BAnd (l r:BExp)
  .
Definition isBool b :=
  match b with
    | BCon _ => true
    | _ => false
  end.
Inductive Stmt :=
  | Skip
  | SAssign (x:string) (e:Exp)
  | HAssign (e:Exp) (e2:Exp)
  | Seq (s1 s2 : Stmt)
  | SIf (b:BExp) (sthn sels : Stmt)
  | SWhile (b:BExp) (body:Stmt)
  | Jump (target : string)
  .


(* K definitions *)
Inductive freezer : Set :=
  | Fplusl : Exp -> freezer
  | Fplusr : Exp -> freezer
  | Fminusl : Exp -> freezer
  | Fminusr : Exp -> freezer
  | Fdivl : Exp -> freezer
  | Fdivr : Exp -> freezer
  | Flel : Exp -> freezer
  | Fler : Z -> freezer
  | Fandl : BExp -> freezer
  | Fassign : string -> freezer
  | Fhassignl : Exp -> freezer
  | Fhassignr : Exp -> freezer
  | Fseq : Stmt -> freezer
  | Fif : Stmt -> Stmt -> freezer
  .

Inductive kitem : Set :=
  | KExp (e : Exp)
  | KBExp (b : BExp)
  | KStmt (s : Stmt)
  | KFreezer (f : freezer)
  | KFreezeE (f : Exp -> kitem)
  | KFreezeB (f : BExp -> kitem)
  .

Definition kra : kitem -> list kitem -> list kitem := @cons kitem.
Definition kdot : list kitem := nil.

Structure kcfg := KCfg {
  kcell : list kitem;
  store : Map string Z;
  heap : Map Z Z;
  labels : Map string Stmt
  }.
