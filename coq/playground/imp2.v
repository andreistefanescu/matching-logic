Module Imp.

Definition Int := nat.

Definition Id := nat.

Require Import Arith.

Definition beq_id := beq_nat.

Inductive AExp : Set :=
  | BaseInt : Int -> AExp
  | BaseId : Id -> AExp
  | Plus : AExp -> AExp -> AExp
  | Div : AExp -> AExp -> AExp
  | AExpHole : AExp.

Inductive BExp : Set :=
  | BaseBool : bool -> BExp
  | Lt : AExp -> AExp -> BExp
  | Not : BExp -> BExp
  | And : BExp -> BExp -> BExp
  | BExpHole : BExp.

Inductive Stmt : Set :=
  | Skip : Stmt
  | Assign : Id -> AExp -> Stmt
  | Seq : Stmt -> Stmt -> Stmt
  | IfThenElse : BExp -> Stmt -> Stmt -> Stmt
  | WhileDo : BExp -> Stmt -> Stmt
  | StmtHole : Stmt.

Require Export List.

Definition Ids := list Id.

Inductive Pgm : Set :=
  | Program : Ids -> Stmt -> Pgm.

Inductive K : Set :=
  | KAExp : AExp -> K
  | KBExp : BExp -> K
  | KStmt : Stmt -> K
  | KIds : Ids -> K
  | KPgm : Pgm -> K
  | KSeq : K -> K -> K
  | KNothing : K.

Inductive MapBaseIdBaseInt : Set :=
  | EmptyMap : MapBaseIdBaseInt
  | ConsMap : Id -> Int -> MapBaseIdBaseInt -> MapBaseIdBaseInt.

Definition Cfg : Set := prod K MapBaseIdBaseInt.

Require Import List.

Local Notation "[ ]" := nil : list_scope.
Local Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..) : list_scope.

Definition iIds : Ids := [ 1 ; 2 ; 3 ].

Definition iPgm : Pgm := (Program iIds (Assign 1 (BaseInt 2))).

Definition iCfg : Cfg := (KSeq (KPgm iPgm) KNothing, EmptyMap).

Fixpoint isResultAExp (aexp : AExp) : bool :=
  match aexp with
    | BaseInt _ => true
    | _ => false
  end.

Fixpoint isResultBExp (bexp : BExp) : bool :=
  match bexp with
    | BaseBool _ => true
    | _ => false
  end.

Fixpoint heatAExp (aexp : AExp) : K :=
  match aexp with
    | BaseInt i => KAExp (BaseInt i)
    | BaseId i => KAExp (BaseId i)
    | Plus aexp1 aexp2 =>
      if isResultAExp aexp1 then
        if isResultAExp aexp2 then
          KAExp (Plus aexp1 aexp2)
        else
          KSeq (KAExp aexp2) (KAExp (Plus aexp1 AExpHole))
      else
        KSeq (KAExp aexp1) (KAExp (Plus AExpHole aexp2))
    | Div aexp1 aexp2 =>
      if isResultAExp aexp1 then
        if isResultAExp aexp2 then
          KAExp (Div aexp1 aexp2)
        else
          KSeq (KAExp aexp2) (KAExp (Div aexp1 AExpHole))
      else
        KSeq (KAExp aexp1) (KAExp (Div AExpHole aexp2))
    | AExpHole =>
      KAExp AExpHole
  end.

Fixpoint heatBExp (bexp : BExp) : K :=
  match bexp with
    | BaseBool b => KBExp (BaseBool b)
    | Lt aexp1 aexp2 =>
      if isResultAExp aexp1 then
        if isResultAExp aexp2 then
          KBExp (Lt aexp1 aexp2)
        else
          KSeq (KAExp aexp2) (KBExp (Lt aexp1 AExpHole))
      else
        KSeq (KAExp aexp1) (KBExp (Lt AExpHole aexp2))
    | Not bexp =>
      if isResultBExp bexp then
        KBExp (Not bexp)
      else
        KSeq (KBExp bexp) (KBExp (Not BExpHole))
    | And bexp1 bexp2 =>
      if isResultBExp bexp1 then
        KBExp (And bexp1 bexp2)
      else
        KSeq (KBExp bexp1) (KBExp (And BExpHole bexp2))
    | BExpHole =>
      KBExp BExpHole
  end.

Fixpoint heatStmt (stmt : Stmt) : K :=
  match stmt with
    | Skip => KStmt Skip
    | Assign id aexp => 
      if isResultAExp aexp then
        KStmt (Assign id aexp)
      else
        KSeq (KAExp aexp) (KStmt (Assign id AExpHole))
    | Seq stmt1 stmt2 =>
      KStmt (Seq stmt1 stmt2)
    | IfThenElse bexp stmt1 stmt2 =>
      if isResultBExp bexp then
        KStmt (IfThenElse bexp stmt1 stmt2)
      else
        KSeq (KBExp bexp) (KStmt (IfThenElse BExpHole stmt1 stmt2))
    | WhileDo bexp stmt =>
      KStmt (WhileDo bexp stmt)
    | StmtHole =>
      KStmt StmtHole
  end.

Definition heatIds (ids : Ids) : K := KIds ids.

Fixpoint isResultStmt (stmt : Stmt) : bool :=
  match stmt with
    _ => false
  end.

Fixpoint heatPgm (pgm : Pgm) : K :=
  match pgm with
    | Program ids stmt =>
      KPgm (Program ids stmt)
  end.

Fixpoint heat  (k : K) : K :=
  match k with
    | KAExp aexp => heatAExp aexp
    | KBExp bexp => heatBExp bexp
    | KStmt stmt => heatStmt stmt
    | KIds Ids => heatIds Ids
    | KPgm pgm => heatPgm pgm
    | KSeq k1 k2 => KSeq (heat k1) k2
    | KNothing => KNothing
  end.

Fixpoint heatCfg (c : Cfg) : Cfg :=
  match c with
    | (k, m) => (heat k, m)
  end.

Fixpoint lookup (m : MapBaseIdBaseInt) (x : Id) : option Int :=
  match m with
    | EmptyMap => None
    | ConsMap y i rest =>
      if beq_id x y then
        Some i
      else
        lookup rest x
  end.

Definition update (m : MapBaseIdBaseInt) (x : Id) (i : Int) : MapBaseIdBaseInt :=
  ConsMap x i m.

Fixpoint keys (m : MapBaseIdBaseInt) : list Id :=
  match m with
    | EmptyMap => []
    | ConsMap x _ rest => x :: (keys rest)
  end.

Definition rw_lookup (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KAExp (BaseId x)) rest, map) =>
      match lookup map x with
        | Some i => Some (KSeq (KAExp (BaseInt i)) rest, map)
        | None => None
      end
    | _ => None
  end.

Definition rw_plus (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KAExp (Plus aexp1 aexp2)) rest, map) =>
      match (aexp1, aexp2) with
        | (BaseInt i1, BaseInt i2) =>
          Some (KSeq (KAExp (BaseInt (i1 + i2))) rest, map)
        | _ =>
          None
      end
    | _ => None
  end.

Definition rw_div (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KAExp (Div aexp1 aexp2)) rest, map) =>
      match (aexp1, aexp2) with
        | (BaseInt i1, BaseInt i2) =>
          if beq_nat i2 0 then
            None
          else
            Some (KSeq (KAExp (BaseInt (i1 + i2))) rest, map)
        | _ =>
          None
      end
    | _ => None
  end.

Definition rw_lt (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KBExp (Lt aexp1 aexp2)) rest, map) =>
      match (aexp1, aexp2) with
        | (BaseInt i1, BaseInt i2) =>
          Some (KSeq (KBExp (BaseBool (leb i1 i2))) rest, map)
        | _ =>
          None
      end
    | _ => None
  end.

Definition rw_not (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KBExp (Not bexp)) rest, map) =>
      match bexp with
        | BaseBool b =>
          Some (KSeq (KBExp (BaseBool (negb b))) rest, map)
        | _ =>
          None
      end
    | _ => None
  end.

Definition rw_and1 (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KBExp (And bexp1 bexp2)) rest, map) =>
      match bexp1 with
        | BaseBool true =>
            Some (KSeq (KBExp bexp2) rest, map)
        | _ =>
          None
      end
    | _ => None
  end.
    
Definition rw_and2 (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KBExp (And bexp1 bexp2)) rest, map) =>
      match bexp1 with
        | BaseBool false =>
            Some (KSeq (KBExp (BaseBool false)) rest, map)
        | _ =>
          None
      end
    | _ => None
 end.

Definition rw_skip (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KStmt Skip) rest, map) =>
      Some (rest, map)
    | _ => None
  end.

Definition rw_assign (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KStmt (Assign id aexp)) rest, map) =>
      match aexp with
        | BaseInt i =>
          match lookup map id with
            | Some _ =>
              Some (rest, update map id i)
            | None =>
              None
          end
        | _ =>
          None
      end
    | _ =>
      None
  end.

Definition rw_sequential (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KStmt (Seq stmt1 stmt2)) rest, map) =>
      Some (KSeq (KSeq (KStmt stmt1) (KStmt stmt2)) rest, map)
    | _ =>
      None
  end.

Definition rw_if_true (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KStmt (IfThenElse (BaseBool true) stmt1 stmt2)) rest, map) =>
      Some (KSeq (KStmt stmt1) rest, map)
    | _ =>
      None
  end.

Definition rw_if_false (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KStmt (IfThenElse (BaseBool false) stmt1 stmt2)) rest, map) =>
      Some (KSeq (KStmt stmt2) rest, map)
    | _ =>
      None
  end.

Definition rw_while (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KStmt (WhileDo bexp stmt)) rest, map) =>
      Some (KSeq (KStmt (IfThenElse bexp (Seq stmt (WhileDo bexp stmt)) Skip)) rest, map)
    | _ =>
      None
  end.

Fixpoint contains l x : bool :=
  match l with
    | [] => false
    | y :: rest =>
      if beq_nat x y then
        true
      else
        contains rest x
  end.

Definition rw_program_still_vars (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KPgm (Program (x :: xs) stmt)) rest, map) =>
      if contains (keys map) x then
        None
      else
        Some (KSeq (KPgm (Program xs stmt)) rest, update map x 0)
    | _ => None
  end.

Definition rw_program_no_vars (c : Cfg) : option Cfg :=
  match c with
    | (KSeq (KPgm (Program [] stmt)) rest, map) =>
      Some (KSeq (KStmt stmt) rest, map)
    | _ => None
  end.

Eval simpl in heatCfg iCfg.

Definition rewrite_rules := [
  rw_program_still_vars;
  rw_program_no_vars;
  rw_lookup;
  rw_plus;
  rw_div;
  rw_lt;
  rw_not;
  rw_and1;
  rw_and2;
  rw_skip;
  rw_assign;
  rw_sequential;
  rw_if_true;
  rw_if_false;
  rw_while
  ].

Definition execute_rule (c : Cfg) rule : option Cfg :=
  rule c.

Fixpoint execute_one_rule (c : Cfg) rules : option Cfg :=
  match rules with
    | [] => None
    | rule :: rest =>
      match execute_rule c rule  with
        | Some c' => Some c'
        | None => execute_one_rule c rest
      end
  end.

Definition execute_one_step (c : Cfg) : option Cfg :=
  execute_one_rule (heatCfg c) rewrite_rules.

Fixpoint execute_many_steps (n : nat) (c : Cfg) : option Cfg := 
  match n with
    | 0 => Some c
    | S n' =>
      match execute_one_step c with
        | Some c' => execute_many_steps n' c'
        | None => None
      end
  end.

Definition hCfg := (heatCfg iCfg).
Eval compute in hCfg.

Definition hCfg1 := execute_one_step hCfg.
Eval compute in hCfg1.

Definition coerce (f : Cfg -> option Cfg) (c : option Cfg) : option Cfg :=
  match c with
    | None => None
    | Some c' => f c'
  end.

Definition hCfg2 := coerce execute_one_step hCfg1.
Eval compute in hCfg2.

Definition hCfg3 := coerce execute_one_step hCfg2.
Eval compute in hCfg3.

Definition hCfg4 := coerce execute_one_step hCfg3.
Eval compute in hCfg4.

Definition hCfg5 := coerce execute_one_step hCfg4.
Eval compute in hCfg5.

End Imp.

Extraction Imp.
