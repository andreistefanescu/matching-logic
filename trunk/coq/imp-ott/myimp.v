Definition var := nat.

Require Import ZArith.

Scheme Equality for nat.
Scheme Equality for bool.

Inductive aexp : Set :=
  | aexp_Int : Z -> aexp
  | aexp_Var : var -> aexp
  | aexp_Plus : aexp -> aexp -> aexp
  | aexp_Div : aexp -> aexp -> aexp.

Lemma aexp_eq_dec : forall a a' : aexp,
  { a = a' } + { a <> a' }.
intros.
decide equality.
apply Z_eq_dec.
apply nat_eq_dec.
Qed.

Fixpoint is_value_aexp (ae : aexp):  bool :=
  match ae with
    | aexp_Int _ => true
    | _ => false
  end.

Inductive bexp : Set :=
  | bexp_Bool : bool -> bexp
  | bexp_Less : aexp -> aexp -> bexp
  | bexp_Not : bexp -> bexp
  | bexp_And : bexp -> bexp -> bexp.

Lemma bexp_eq_dec : forall b b' : bexp,
  { b = b' } + { b <> b' }.
intros.
decide equality.
apply bool_eq_dec.
apply aexp_eq_dec.
apply aexp_eq_dec.
Qed.

Fixpoint is_value_bexp (be : bexp):  bool :=
  match be with
    | bexp_Bool _ => true
    | _ => false
  end.

Inductive stmt : Set :=
  | stmt_Skip : stmt
  | stmt_Assign : var -> aexp -> stmt
  | stmt_Seq : stmt -> stmt -> stmt
  | stmt_Ite : bexp -> stmt -> stmt -> stmt
  | stmt_While : bexp -> stmt -> stmt.

Lemma stmt_eq_dec : forall s s' : bexp,
  { s = s' } + { s <> s' }.
intros.
decide equality.
apply bool_eq_dec.
apply aexp_eq_dec.
apply aexp_eq_dec.
Qed.

Fixpoint is_value_stmt (s : stmt):  bool :=
  match s with
    | stmt_Skip => true
    | _ => false
  end.

Inductive pgm : Set :=
  | pgm_Program : list var -> stmt -> pgm.

Lemma pgm_eq_dec : forall p p' : bexp,
  { p = p' } + { p <> p' }.
intros.
decide equality.
apply bool_eq_dec.
apply aexp_eq_dec.
apply aexp_eq_dec.
Qed.

Fixpoint is_value_pgm (p : pgm) : bool :=
  match p with
    | pgm_Program l s =>
      match l with
        | nil => is_value_stmt s
        | _ => false
      end
  end.

Inductive type : Set :=
  | t_aexp : type
  | t_bexp : type
  | t_stmt : type
  | t_pgm : type.

Definition t_denote (t : type) : Set :=
  match t with
  | t_aexp => aexp
  | t_bexp => bexp
  | t_stmt => stmt
  | t_pgm => pgm
  end.

Definition is_value (t : type) : (t_denote t) -> bool :=
  match t with
    | t_aexp => is_value_aexp
    | t_bexp => is_value_bexp
    | t_stmt => is_value_stmt
    | t_pgm => is_value_pgm
  end.

Inductive E { hole_t : type } : type -> Set :=
  | E_Hole :
    E hole_t

  | E_PlusL (ae : aexp) :
    (E t_aexp) -> E t_aexp
  | E_PlusR (ae : aexp) :
    (* is_value_aexp ae = true -> *)
    (E t_aexp) -> E t_aexp

  | E_DivL (ae : aexp) :
    (E t_aexp) -> E t_aexp
  | E_DivR (ae : aexp) :
    (* is_value_aexp ae = true -> *)
    (E t_aexp) -> E t_aexp

  | E_LessL (ae : aexp) :
    (E t_aexp) -> E t_bexp
  | E_LessR (ae : aexp) :
    (* is_value_aexp ae = true -> *)
    (E t_aexp) -> E t_bexp

  | E_Not :
    (E t_bexp) -> E t_bexp

  | E_AndL (be : bexp) :
    (E t_bexp) -> E t_bexp
  | E_AndR (be : bexp) :
    (* is_value_bexp be = true -> *)
    (E t_bexp) -> E t_bexp
    
  | E_SeqL :
    stmt -> (E t_stmt) -> E t_stmt

  | E_Pgm :
    (E t_stmt) -> E t_pgm.

Fixpoint fill t t' (ec : @E t t') (e : t_denote t) : t_denote t' :=
  match ec with
    | E_Hole => e
    | E_PlusL ae ec' => aexp_Plus (fill t t_aexp ec' e) ae
    | E_PlusR ae ec' => aexp_Plus ae (fill t t_aexp ec' e)
    | E_DivL ae ec' => aexp_Div (fill t t_aexp ec' e) ae
    | E_DivR ae ec' => aexp_Div ae (fill t t_aexp ec' e)

    | E_LessL ae ec' => bexp_Less (fill t t_aexp ec' e) ae
    | E_LessR ae ec' => bexp_Less ae (fill t t_aexp ec' e)
    | E_Not ec' => bexp_Not (fill t t_bexp ec' e)
    | E_AndL be ec' => bexp_And (fill t t_bexp ec' e) be
    | E_AndR be ec' => bexp_And be (fill t t_bexp ec' e)

    | E_SeqL s ec' => stmt_Seq (fill t t_stmt ec' e) s

    | E_Pgm ec' => pgm_Program nil (fill t t_stmt ec' e)
  end.

Check @E_Hole.
Check (@E_Hole t_aexp).

Require Import Bool.
Require Import CpdtTactics.

Fixpoint split_aexp (a : aexp) : option (@E t_aexp t_aexp * aexp)%type :=
  match a with
    | aexp_Var x => Some (@E_Hole t_aexp, aexp_Var x)
    | aexp_Int z => None
    | aexp_Plus a1 a2 =>
      match split_aexp a1 with
        | None =>
          match split_aexp a2 with         
            | None => Some (@E_Hole t_aexp, aexp_Plus a1 a2)
            | Some (ec, a') => Some ((E_PlusR a1 ec), a')
          end
        | Some (ec, a') =>
          Some (E_PlusL a2 ec, a')
      end
    | aexp_Div a1 a2 =>
      match split_aexp a1 with
        | None =>
          match split_aexp a2 with         
            | None => Some (@E_Hole t_aexp, aexp_Div a1 a2)
            | Some (ec, a') => Some ((E_DivR a1 ec), a')
          end
        | Some (ec, a') =>
          Some (E_DivL a2 ec, a')
      end
  end.

Lemma split_aexp_correct : forall a,
  ((split_aexp a = None) -> is_value_aexp a = true) /\
  (forall ec a',
    (split_aexp a = Some (ec, a') ->
      (fill t_aexp t_aexp ec a' = a) /\
      is_value_aexp a' = false)).
Proof.
  Local Hint Extern 10 (_ = _) => match goal with
    | [ H : context[match ?E with pair _ _ => _ end] |- _ ] =>
      destruct E; crush
  end.
  Local Hint Extern 10 (_ = _) => match goal with
    | [ H : context[match ?E with Some _ => _ | None => _ end] |- _ ] =>
      let x := fresh "s" in 
        remember (E) as x; destruct x; crush
  end.
  Local Hint Extern 10 (aexp_Plus _ _ = aexp_Plus _ _) => f_equal;
    match goal with
      | [ H : _ |- _ ] => apply H; crush
    end.
  Local Hint Extern 10 (is_value_aexp _ = _) =>
    match goal with
      | [ H : context[Some (pair ?E ?A) = Some (pair _ _) -> fill _ _ _ _ = _ /\ is_value_aexp _ = _] |- _ ] => specialize (H E A (eq_refl _ )); decompose [and] H; crush
    end.
  Local Hint Extern 10 (aexp_Div _ _ = aexp_Div _ _) => f_equal;
    match goal with
      | [ H : _ |- _ ] => apply H; crush
    end.
  induction a; crush.
Qed.

Fixpoint split_bexp (be : bexp) : option { t : type & (@E t t_bexp * (t_denote t))%type } :=
  match be with
    | bexp_Bool b => None
    | bexp_And be1 be2 =>
      match split_bexp be1 with
        | None =>
          match split_bexp be2 with
            | None => Some (existT _ t_bexp (E_Hole, bexp_And be1 be2))
            | Some (existT t (ec, e)) => Some (existT _ t (E_AndR be1 ec, e))
          end
        | Some (existT t (ec, e)) => Some (existT _ t (E_AndL be2 ec, e))
      end
    | bexp_Less ae1 ae2 =>
      match split_aexp ae1 with
        | None =>
          match split_aexp ae2 with
            | None => Some (existT _ t_bexp (E_Hole, bexp_Less ae1 ae2))
            | Some (ec, e) => Some (existT _ t_aexp (E_LessR ae1 ec, e))
          end
        | Some (ec, e) => Some (existT _ t_aexp (E_LessL ae2 ec, e))
      end
    | bexp_Not be =>
      match split_bexp be with
        | None => Some (existT _ t_bexp (E_Hole, bexp_Not be))
        | Some (existT t (ec, e)) => Some (existT _ t (E_Not ec, e))
      end
  end.


Scheme Bexp_rect_dep := Induction for bexp Sort Type.

Scheme sigT_rect_dep := Induction for sigT Sort Type.

Lemma belea' : forall t t',
  t = t' -> t_denote t = t_denote t'.
intros.
rewrite H.
reflexivity.
Qed.

(* Definition property (t : type) := t_denote t -> Prop. *)

(* Check property. *)
(* Print property. *)


(* Lemma belea : forall t, forall (P : property t), *)
(*   forall t', *)
(*     P (t_denote t) -> *)
(*     t = t' -> *)
(*     P (t_denote t'). *)
    
(* Derive Inversion leminv with (forall t ec e0 a0, *)
(*   @eq (@sigT type (fun x : type => @E x t_bexp)) *)
(*          (@existT type (fun x : type => @E x t_bexp) t_aexp *)
(*             (@E_LessL t_aexp a0 e0)) *)


Lemma type_dec : forall t t' : type,
  { t = t' } + { t <> t' }.
decide equality.
Qed.

Lemma split_bexp_correct : forall be,
  ((split_bexp be = None) -> is_value_bexp be = true) /\
  (forall t : type,
    forall (ec : @E t t_bexp) (e : t_denote t),
    (split_bexp be = Some (existT _ t (ec, e)) ->
      (fill t t_bexp ec e = be) /\
      is_value t e = false)).
Proof.
  simpl.
  induction be.
  crush.
  split.
  crush.
  intros.
  split.
  simpl in H.
  remember (split_aexp a) as s.
  destruct s.
  destruct p.
  inversion H.
  Require Import EqdepFacts.
  simpl.

  Require Import Eqdep_dec.
  Set Printing All.
  simpl.

  assert (@eq Set (@E t t_bexp) (@E t_aexp t_bexp)).
  rewrite H1.
  reflexivity.

  Check (inj_pair2_eq_dec type type_dec).

  Check (inj_pair2_eq_dec type type_dec (fun t : type => @E t t_bexp) t_aexp
    (@E_LessL t_aexp a0 e0) ec).
  simpl.
  
  Hint Extern 0 (_ = _) => match goal with
    | [ H : context[match ?E with pair _ _ => _ end] |- _ ] =>
      destruct E; crush
  end.
  Hint Extern 0 (_ = _) => match goal with
    | [ H : context[match ?E with Some _ => _ | None => _ end] |- _ ] =>
      let x := fresh "s" in
        remember (E) as x; destruct x; crush
  end.
  Hint Extern 10 (bexp_Less _ _ = bexp_Less _ _) => f_equal;
    match goal with
      | [ H : _ |- _ ] => apply H; crush
    end.
  (* Hint Extern 10 (is_value_aexp _ = _) => *)
  (*   match goal with *)
  (*     | [ H : context[Some (pair ?E ?A) = Some (pair _ _) -> fill _ _ _ _ = _ /\ is_value_aexp _ = _] |- _ ] => specialize (H E A (eq_refl _ )); decompose [and] H; crush *)
  (*   end. *)
  (* Hint Extern 10 (aexp_Div _ _ = aexp_Div _ _) => f_equal; *)
  (*   match goal with *)
  (*     | [ H : _ |- _ ] => apply H; crush *)
  (*   end. *)
  induction be using Bexp_rect_dep.
  crush.
  split. crush. simpl. intros. split.  
  match goal with
    | [ H : context[match ?E with Some _ => _ | None => _ end] |- _ ] =>
      let x := fresh "s" in
        remember (E) as x; destruct x
  end.
match goal with
    | [ H : context[match ?E with pair _ _ => _ end] |- _ ] =>
      destruct E
  end.
simpl.
simpl in H.
inversion H.
Set Printing All.
simpl.
Derive Inversion leminv with (forall t ec e0 a0,
  @eq (@sigT type (fun x : type => @E x t_bexp))
         (@existT type (fun x : type => @E x t_bexp) t_aexp
            (@E_LessL t_aexp a0 e0))
         (@existT type (fun x : type => @E x t_bexp) t ec)).
Check leminv.

injection H2.
inversion H2 using leminv.
assert (bexp (fill t t_bexp (@E_LessL t a0 e0) e) (bexp_Less a a0)).
Check sigT_rect_dep.
rewrite <- H1 in H2.
inversion H2 using (@sigT_rect_dep type t_denote).
rewrite H1 in H.
Set Printing All.
assert (t = t_aexp -> (ec : @E t) = ((E_LessL a0 e0) : @E t_aexp t_bexp)).
Qed.

Lemma split_bexp_correct : forall be,


Inductive env : Set :=
  | env_Empty : env
  | env_Bind : var -> Z -> env -> env.

Inductive binds : var -> Z -> env -> Prop :=
  | binds_Base : forall v z e,
    binds v z (env_Bind v z e)
  | binds_Rec : forall v v' z z' e,
    not (eq v v') ->
    binds v z e ->
    binds v z (env_Bind v' z' e).

Definition configuration t := (t_denote t * env)%type.

Inductive basic_step_aexp : configuration t_aexp -> configuration t_aexp -> Prop :=
| Plus :
  forall z1 z2 e,
    basic_step_aexp (aexp_Plus (aexp_Int z1) (aexp_Int z2), e) (aexp_Int (Zplus z1 z2), e)
| Lookup :
  forall z v e,
    binds v z e ->
    basic_step_aexp (aexp_Var v, e) (aexp_Int z, e)
| Div :
  forall z1 z2 e,
    Zeq_bool z2 0 = false ->
    basic_step_aexp (aexp_Div (aexp_Int z1) (aexp_Int z2), e) (aexp_Int (Zdiv z1 z2), e)
with basic_step_bexp : configuration t_bexp -> configuration t_bexp -> Prop :=
| Not :
  forall b e,
    basic_step_bexp ((bexp_Not (bexp_Bool b)), e) ((bexp_Bool (negb b)), e)
| And :
  forall b1 b2 e,
    basic_step_bexp (bexp_And (bexp_Bool b1) (bexp_Bool b2), e) (bexp_Bool (andb b1 b2), e)
| Less :
  forall z1 z2 e,
    basic_step_bexp (bexp_Less (aexp_Int z1) (aexp_Int z2), e) (bexp_Bool (Zle_bool z1 z2), e)
with basic_step_stmt : configuration t_stmt -> configuration t_stmt -> Prop :=
| Assign :
  forall v z e,
    basic_step_stmt (stmt_Assign v (aexp_Int z), e) (stmt_Skip, env_Bind v z e)
| Seq :
  forall s e,
    basic_step_stmt (stmt_Seq stmt_Skip s, e) (s, e)
| Ite_true :
  forall s1 s2 e,
    basic_step_stmt (stmt_Ite (bexp_Bool true) s1 s2, e) (s1, e)
| Ite_false :
  forall s1 s2 e,
    basic_step_stmt (stmt_Ite (bexp_Bool false) s1 s2, e) (s2, e)
| While :
  forall b s e,
    basic_step_stmt (stmt_While b s, e) (stmt_Ite b (stmt_Seq s (stmt_While b s)) stmt_Skip, e)
with basic_step_pgm : configuration t_pgm -> configuration t_pgm -> Prop :=
| DeclareVar :
  forall lv s e v,
    basic_step_pgm (pgm_Program (cons v lv) s, e) (pgm_Program lv s, env_Bind v 0%Z e).

Definition basic_step (t : type) : (configuration t) -> (configuration t) -> Prop :=
  match t with
    | t_aexp => basic_step_aexp
    | t_bexp => basic_step_bexp
    | t_stmt => basic_step_stmt
    | t_pgm => basic_step_pgm
  end.

Inductive full_step : configuration t_pgm -> configuration t_pgm -> Prop :=
| Context :
  forall e e' : env,
    forall t_exp (exp exp' : t_denote t_exp),
      basic_step t_exp (exp, e) (exp', e') ->
      forall ec : @E t_exp t_pgm,
        full_step ((fill t_exp t_pgm ec exp), e) ((fill t_exp t_pgm ec exp'), e').

Require Import Relation_Definitions.
Require Import Relation_Operators.

Definition results p e p' e' :=
  (clos_refl_trans _ full_step (p, e) (p', e')) /\ is_value_pgm p' = true.

Notation X := 0.
Notation Y := 1.
Notation Z := 2.
Notation "a + b" := (aexp_Plus a b).
Notation "a / b" := (aexp_Div a b).
Notation "a && b" := (bexp_And a b).
Notation "! b" := (bexp_Not b) (at level 60).
Notation "a <= b" := (bexp_Less a b).
Notation Skip := (stmt_Skip).
Notation "a ; b" := (stmt_Seq a b) (at level 60, right associativity).
Notation "v <- a" := (stmt_Assign v a) (at level 60).
Notation "'if' b 'then' s1 'else' s2" := (stmt_Ite b s1 s2) (at level 60).
Notation "'while' b 'do' s" := (stmt_While b s) (at level 60).
Notation "'val' z" := (aexp_Int z) (at level 60).
Notation "'VAR' v" := (aexp_Var v) (at level 60).
Notation "'declare' l 'program' p" := (pgm_Program l p) (at level 60).

Notation "[ ]" := nil.
Notation "a :: b" := (cons a b).
Notation "[ a , .. , b ]" := (a :: .. (b :: []) ..).

Definition simple_program :=
  (
    declare
      ( [ X , Y , Z ] )
    program (
      (X <- val 10) ;
      (Y <- val 20) ;
      (Z <- (VAR X) + (VAR Y))
    )
  ).

Definition empty_program :=
  (
    declare ( [] )
    program ( stmt_Skip )
  ).

Example ex1 :
  exists env,
    results simple_program env_Empty empty_program env /\
    binds Z 30 env.
remember (env_Bind Z 0 (env_Bind Y 0 (env_Bind X 0 env_Empty))) as env_Init.
exists (env_Bind Z 30 (env_Bind Y 20 (env_Bind X 0 env_Init))).
unfold results.
split.
split.
eapply rt_step.
unfold simple_program.
