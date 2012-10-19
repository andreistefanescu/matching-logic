Require Import BinPos.
Require Import ZArith.
Require Import FMapPositive.

Set Implicit Arguments.

Inductive Var := var (p : positive).
Definition var_dec : forall (x y : Var), {x=y}+{x<>y}. 
intros. decide equality. apply positive_eq_dec.
Qed.

Definition Val := Z.
Definition Store := PositiveMap.t Val.
Definition lookup (env : Store) (v : Var) : Z :=
  match v with
    | var key =>
      match PositiveMap.find key env with
        | Some x => x
        | None => 0%Z
      end
  end.
Definition update (env : Store) (v : Var) i :=
  match v with
    | var key => PositiveMap.add key i env
  end.

Inductive Exp :=
  | EVar (v:Var)
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
  | SAssign (x:Var) (e:Exp)
  | Seq (s1 s2 : Stmt)
  | SIf (b:BExp) (sthn sels : Stmt)
  | SWhile (b:BExp) (body:Stmt)
  .
Inductive cfg :=
  | Cfg : Stmt -> Store -> cfg
  .

Inductive sosCfg :=
  | SCfg : Stmt -> Store -> sosCfg
  | ECfg : Exp -> Store -> sosCfg
  | BCfg : BExp -> Store -> sosCfg
  .

Inductive freezer : Set :=
  | Fplusl : Exp -> freezer
  | Fplusr : Exp -> freezer
  | Fdivl : Exp -> freezer
  | Fdivr : Exp -> freezer
  | Flel : Exp -> freezer
  | Fler : Z -> freezer
  | Fandl : BExp -> freezer
  | Fassign : Var -> freezer
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
  | KCfg : list kitem -> Store -> kcfg.

Section Ctxt.

  Variable A : Set.
  Inductive ctxt : Set -> Set :=
  | hole : ctxt A
  | plusl : ctxt Exp -> Exp -> ctxt Exp
  | plusr : Exp -> ctxt Exp -> ctxt Exp
  | divl : ctxt Exp -> Exp -> ctxt Exp
  | divr : Exp -> ctxt Exp -> ctxt Exp
  | lel : ctxt Exp -> Exp -> ctxt BExp
  | ler : Z -> ctxt Exp -> ctxt BExp
  | andl : ctxt BExp -> BExp -> ctxt BExp
  | assigne : Var -> ctxt Exp -> ctxt Stmt
  | seqc : ctxt Stmt -> Stmt -> ctxt Stmt
  | ifc : ctxt BExp -> Stmt -> Stmt -> ctxt Stmt
  | whilec : ctxt BExp -> Stmt -> ctxt Stmt
  | cfgc : ctxt Stmt -> Store -> ctxt cfg
  .
  Fixpoint plug (R : Set) (c : ctxt R) (a : A) : R :=
    match c with
  | hole => a
  | plusl cl r => EPlus (plug cl a) r
  | plusr l cr => EPlus l (plug cr a)
  | divl cl r => EDiv (plug cl a) r
  | divr l cr => EDiv l (plug cr a)
  | lel cl r => BLe (plug cl a) r
  | ler i cr => BLe (ECon i) (plug cr a)
  | andl cl r => BAnd (plug cl a) r
  | assigne v ce => SAssign v (plug ce a)
  | seqc cs s2 => Seq (plug cs a) s2
  | ifc cc s1 s2 => SIf (plug cc a) s1 s2
  | whilec cc b => SWhile (plug cc a) b
  | cfgc cs env => Cfg (plug cs a) env
  end.
End Ctxt.