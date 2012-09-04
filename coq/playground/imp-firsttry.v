(* 
1) labeled repr.

2) executable

- matching
- K, subsorting
- configuration abstraction
- K bindings/substitution (HOAS?)
- freshness
- builtin primitives


- 
*)

Definition int := nat.

Inductive id : Set :=
  Id : int -> id.

Fixpoint beq_int (n m : int) : bool :=
  match (n, m) with
    | (0, 0) => true
    | (S _, 0) => false
    | (0, S _) => false
    | (S n', S m') => beq_int n' m'
  end.

Definition bneq_int (n m : int) : bool := negb (beq_int n m).

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_int n1 n2
  end.

Definition bneq_id X1 X2 := negb (beq_id X1 X2).

Inductive AExp : Set :=
  | c_int : int -> AExp
  | c_id : id -> AExp
  | c_plus : AExp -> AExp -> AExp
  | c_div : AExp -> AExp -> AExp.

Inductive BExp : Set :=
  | c_bool : bool -> BExp
  | c_le : AExp -> AExp -> BExp
  | c_not : BExp -> BExp
  | c_and : BExp -> BExp -> BExp.

Inductive Stmt : Set :=
  | c_skip : Stmt
  | c_assignment : id -> AExp -> Stmt
  | c_seq : Stmt -> Stmt -> Stmt
  | c_ifthenelse : BExp -> Stmt -> Stmt -> Stmt
  | c_while : BExp -> Stmt -> Stmt.

Inductive Ids : Set := 
  | c_listid : list id -> Ids.

Inductive Pgm : Set :=
  | c_pgm : list id -> Stmt -> Pgm.

Inductive K : Set :=
  | k_pgm : Pgm -> K
  | k_Stmt : Stmt -> K
  | k_BExp : BExp -> K
  | k_AExp : AExp -> K

  | k_id : id -> K
  | k_int : int -> K

  | k_hole : K

  | k_list : K -> K -> K.
(*
Inductive Klabel : Set :=
  | l_while : Klabel
  | l_ifthenelse : Klabel
  | l_ifholethenelse : Klabel

Inductive K' : Set :=
  | k_apply : Klabel -> list K' -> K'
  | k_arrow : list K' -> K'.

k_apply plus (1 ~> 2) 3         (*  *)

k_apply l_ifthenelse (k_arrow true 2 3, ... )
*)
(*

    

  l, l1, l3

  exists l2, l = l1 ++ l2 ++ l3

*)

(*

    

    X ~> Y

    X ~> Y + HOLE ~> Z + HOLE

    X1 ~> (X2 ~> ... ~> Xn)
 
*)

Definition is_value (k : K) : bool :=
  match k with
    | k_BExp (c_bool _) => true
    | k_AExp (c_int _) => true
    | _ => false
  end.

Definition configuration : Set := prod K (list (prod id K)).

(*
   record
        k : K
        state : record
                  env : map id K
                end
        threads : list record
                         ...
                       end
        k' : option K
        race : option K
    
*)

(*
mapsto M i k when M maps i into k

identifiers can be K's.
*)

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
    | _ => big
  end.

Inductive transition : configuration -> configuration -> Prop :=
  | lookup : forall (X : id) (I : int) (other : K) (map : list (prod id K)),
               mapsto map X (k_int I) ->
               transition (k_list (k_id X) other, map)
                          (k_list (k_int I) other, map)
  | cool : forall (k : K) (other : K) (map : list (prod id K)),
           is_value k = true ->
           transition (k_list k other, map) (fillhole other k, map).


  | heat_plus_1 : forall (a1 a2 : AExp) (other : K) (map : list (prod id K)),
           transition (k_list (k_AExp (c_plus a1 a2)) other, map)
                      (k_list (k_AExp a1) (k_list (k_AExp (c_plus k_hole a2)) other), map).


