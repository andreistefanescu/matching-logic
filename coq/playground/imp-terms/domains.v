Require Import BinPos.
Require Import ZArith.
Require Import FMapPositive.
Require Import String.

Set Implicit Arguments.

Axiom Map : Set -> Set.
Axiom mapItem : forall {A: Set}, A -> Z -> Map A.
Axiom mapJoin : forall {A : Set}, Map A -> Map A -> Map A.
Axiom mapEmpty : forall {A : Set}, Map A.
Infix ":->" := mapItem (at level 50, no associativity).
Infix ":*" := mapJoin (at level 60, right associativity).
Axiom mapUnit : forall {A} (m : Map A), m :* mapEmpty = m.
Axiom mapComm : forall {A} (m1 m2 : Map A), m1 :* m2 = m2 :* m1.
Axiom mapAssoc : forall {A} (m1 m2 m3 : Map A), (m1 :* m2) :* m3 = m1 :* m2 :* m3.
Lemma mapComAssoc : forall {A} (m1 m2 m3 : Map A), m1 :* m2 :* m3 = m2 :* m1 :* m3.
intros. rewrite <- mapAssoc, (mapComm m1 m2), mapAssoc. reflexivity.
Qed.

(* Language syntax *)
Inductive Exp :=
  | EVar (v:string)
  | ECon (i:Z)
  | EPlus (l r:Exp)
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
  .

(* K definitions *)
Inductive freezer : Set :=
  | Fplusl : Exp -> freezer
  | Fplusr : Exp -> freezer
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
  .

Definition kra : kitem -> list kitem -> list kitem := @cons kitem.
Definition kdot : list kitem := nil.

Inductive kcfg :=
  | KCfg : list kitem -> Map string -> Map Z -> kcfg.