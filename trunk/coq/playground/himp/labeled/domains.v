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

Infix "|->" := mapItem (at level 50, no associativity).
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

Lemma equivUnitL : forall {K V} (m : Map K V), MapEquiv (mapEmpty :* m) m.
intros. rewrite equivComm. apply equivUnit.
Qed.

Lemma equivComAssoc : forall {K V} (m1 m2 m3 : Map K V), m1 :* m2 :* m3 ~= m2 :* m1 :* m3.
intros. rewrite <- equivAssoc, (equivComm m1 m2), equivAssoc. reflexivity. Qed.

Inductive label : Set :=
  | EPlus
  | EMinus
  | EDiv
  | BLe
  | BNot
  | BAnd
  | Skip
  | Seq
  | SAssign
  | HAssign
  | SIf
  | SWhile
  | Jump
  .

Inductive hook_fun : Set :=
  | Z_Z_Z : (Z -> Z -> Z) -> hook_fun
  | Z_Z_bool : (Z -> Z -> bool) -> hook_fun
  | bool_bool : (bool -> bool) -> hook_fun
  .                                     

Definition hook l :=
  match l with
    | EPlus => Some (Z_Z_Z Zplus)
    | EMinus => Some (Z_Z_Z Zminus)
    | BLe => Some (Z_Z_bool Z.leb)
    | BNot => Some (bool_bool negb)
    | _ => None
  end.

Definition is_strict1 l :=
  match l with
  | EPlus | EMinus 
  | EDiv  | BLe
  | BNot  | BAnd
  | SIf => true
  | _ => false
  end.

Definition is_strict2 l :=
  match l with
  | EPlus | EMinus 
  | EDiv  | BLe
  | SAssign | HAssign => true
  | _ => false
  end.

Definition is_sequential l :=
  match l with
    | BLe => true
    | _ => false
  end.

Inductive Ast : Set :=
  | AId (x : string)
  | ABool (b : bool)
  | AInt (i : Z)
  | AApp (l : label) (args : list Ast)
  .

Definition isVal a :=
  match a with
    | AInt _ => true
    | ABool _ => true
    | _ => false
  end.

Inductive kitem : Set :=
  | KAst (a : Ast)
  | KFreezer (f : Ast -> kitem)
  .

Definition kra : kitem -> list kitem -> list kitem := @cons kitem.
Definition kdot : list kitem := nil.

Structure kcfg := KCfg {
  kcell : list kitem;
  store : Map string Z;
  heap : Map Z Z;
  labels : Map string Ast
  }.