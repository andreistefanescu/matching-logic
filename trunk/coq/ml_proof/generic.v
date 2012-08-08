Require Import matchingl.
Require Import NArith.BinPos.
Require Import FMapPositive.
Require Import List.
Require Setoid.

Set Implicit Arguments.

Fixpoint nth_error (A : Set) (l : list A) (ix : nat) : option A :=
  match l, ix with
    | nil, _ => None
    | x :: _, O => Some x
    | _ :: xs, S n => nth_error xs n
  end.

(* plan - take over generic part of term syntax,
   parameterized just on set of labels,
   leaving the type polymorphic in choice of variables.

   generic version takes instantiation with positive
   as the version, but inductive formula defined from
   instantiation with McBride-style free names / bound indices
   representation.



   polymorphic version of formula indexed by number of
   dangling indices
 *)

Module Type Labels.
  Parameter Sort : Set.
  Parameter sort_sem : Sort -> Set.
  Parameter sort_dec : forall (x y:Sort), {x=y}+{x<>y}.
  Fixpoint optype args result :=
    match args with
      | nil => sort_sem result
      | arg :: args => sort_sem arg -> optype args result
    end.
  (*  E v.x      rho = { x=>skip;v } *)
  (*  de Bruijn indices  *)

  Parameter Label : Set.
  Parameter label_sem : Label ->
    {args : list Sort & {result : Sort & optype args result}}.
End Labels.

Module GenericLang(Import Labels : Labels) <: ObjectLanguage.

  Section GenericTerms.
    Variable var : Set.

    Inductive Term : Set :=
    | TMVar (v : var)
    | TApp (l : Label) (ts : list Term).

    Definition term_ind (P : Term -> Prop) (Ps : list Term -> Prop)
      (HVar : forall v, P (TMVar v))
      (HApp : forall l ts, Ps ts -> P (TApp l ts))
      (Hnil : Ps nil)
      (Hcons : forall t ts, P t -> Ps ts -> Ps (t :: ts)) :
      forall t, P t :=
        fix term t :=
        match t as t return P t with
          | TMVar v => HVar v
          | TApp l ts => HApp l ts ((fix terms ts :=
            match ts as ts return Ps ts with
              | nil => Hnil
              | x :: xs => Hcons _ _ (term x) (terms xs)
            end
            ) ts)
        end.

    Definition varpred (P : var -> Prop) : Term -> Prop :=
      fix good (t : Term) :=
      match t with
        | TMVar y => P y
        | TApp l ts => (fix goods ts :=
          match ts with
            | nil => True
            | t :: ts => good t /\ goods ts
          end) ts
      end.
  End GenericTerms.

  Definition app_var rho v :=
    match PositiveMap.find v rho with
      | Some t' => t'
      | None => TMVar v
    end.

  Fixpoint apply {var1 var2 : Set}(subst : var1 -> Term var2) t :=
    match t with
      | TMVar v => subst v
      | TApp l ts => TApp l (map (apply subst) ts)
    end.

  Module Base <: Terms.
    Definition T := Term positive.
    Definition IsVariable (t : Term positive) :=
      match t with
        | TMVar _ => True
        | _ => False
      end.
    Definition Var := {t : T & IsVariable t}.
    Definition Var_var (v : Var) : positive :=
      match v with
        | existT t pf =>
          match t as t return IsVariable t -> positive with
            | TMVar v => fun _ => v
            | TApp _ _ => fun pf => match pf with end
          end pf
      end.
    Definition Substitution := PositiveMap.t (Term positive).
    Definition identity := PositiveMap.empty (Term positive).
    Definition app_var rho v :=
      match PositiveMap.find v rho with
        | Some t' => t'
        | None => TMVar v
      end.
    Definition Apply rho := apply (app_var rho).
    Lemma identity_refl t : Apply identity t = t.
      unfold Apply.
      induction t using term_ind with
        (Ps := fun l => map (apply (app_var identity)) l = l); simpl;
          [unfold app_var; rewrite PositiveMap.gempty| ..]; congruence.
    Qed.

    Definition Update rho v (t : Term positive) := PositiveMap.add (Var_var v) t rho.

    Definition notFreeT v t :=
      let p := Var_var v in
      varpred (fun p' => p <> p') t.
  End Base.

  Inductive TVar : Set :=
    | VFree (p : positive)
    | VBound (ix : nat).

  Definition inTerm : Term positive -> Term TVar :=
    apply (fun v => TMVar (VFree v)).

  Definition Apply' (rho : PositiveMap.t (Term positive)) := apply (fun v =>
    match v with
      | VFree p => inTerm (app_var rho p)
      | VBound ix => TMVar (VBound ix)
    end).

  Module BaseF <: Formulas Base.
    Export Base.

    Inductive FormulaI : Set :=
    | EqualsI : (Term TVar) -> (Term TVar) -> FormulaI
    | AndI : FormulaI -> FormulaI -> FormulaI
    | OrI : FormulaI -> FormulaI -> FormulaI
    | ImpliesI : FormulaI -> FormulaI -> FormulaI
    | ExistsI : FormulaI -> FormulaI
    | HasSortI : Sort -> Term TVar -> FormulaI
    | PatternI : (Term TVar) -> FormulaI.

    Definition bindTVar (v : positive) (ix : nat) (t : TVar) : TVar :=
      match t with
        | VFree f => if positive_eq_dec v f then VBound ix else VFree f
        | VBound b => VBound (if Compare_dec.leb ix b then S b else b)
      end.
    Definition bindTerm (v : positive) (ix : nat) : Term TVar -> Term TVar :=
      apply (fun v' => TMVar (bindTVar v ix v')).

    Fixpoint bindAs (v : positive) (ix : nat) (f : FormulaI) : FormulaI :=
      match f with
        | EqualsI t1 t2 => EqualsI (bindTerm v ix t1) (bindTerm v ix t2)
        | AndI f1 f2 => AndI (bindAs v ix f1) (bindAs v ix f2)
        | OrI f1 f2 => OrI (bindAs v ix f1) (bindAs v ix f2)
        | ImpliesI f1 f2 => ImpliesI (bindAs v ix f1) (bindAs v ix f2)
        | ExistsI f => ExistsI (bindAs v (S ix) f)
        | HasSortI s t => HasSortI s (bindTerm v ix t)
        | PatternI t => PatternI (bindTerm v ix t)
      end.

    Definition Formula := FormulaI.
    Definition Equals t1 t2 := EqualsI (inTerm t1) (inTerm t2).
    Definition And := AndI.
    Definition Or := OrI.
    Definition Implies := ImpliesI.
    Definition Exists v f := ExistsI (bindAs (Var_var v) 0 f).
    Definition HasSort s t := HasSortI s (inTerm t).
    Definition Pattern t := PatternI (inTerm t).

    Fixpoint ApplyF (rho : Substitution) (f : Formula) : Formula :=
      match f with
        | EqualsI t1 t2 => EqualsI (Apply' rho t1) (Apply' rho t2)
        | AndI f1 f2 => AndI (ApplyF rho f1) (ApplyF rho f2)
        | OrI f1 f2 => OrI (ApplyF rho f1) (ApplyF rho f2)
        | ImpliesI f1 f2 => ImpliesI (ApplyF rho f1) (ApplyF rho f2)
        | ExistsI fb => ExistsI (ApplyF rho fb)
        | HasSortI s t => HasSortI s (Apply' rho t)
        | PatternI t => PatternI (Apply' rho t)
      end.

    Definition notFreeTV (p : positive) (v : TVar) : Prop :=
      match v with
        | VFree p' => p <> p'
        | VBound _ => True
      end.

    Definition notFree (v : Var) : Formula -> Prop :=
      let p := Var_var v in
        fix nf f := match f with
                   | EqualsI t1 t2 => varpred (notFreeTV p) t1 /\ varpred (notFreeTV p) t2
                   | AndI f1 f2 => nf f1 /\ nf f2
                   | OrI f1 f2 => nf f1 /\ nf f2
                   | ImpliesI f1 f2 => nf f1 /\ nf f2
                   | ExistsI fb => nf fb
                   | HasSortI s t => varpred (notFreeTV p) t
                   | PatternI t => varpred (notFreeTV p) t
                 end.    

    Fixpoint patternless (f : Formula) : Prop :=
      match f with
        | EqualsI t1 t2 => True
        | AndI f1 f2 => patternless f1 /\ patternless f2
        | OrI f1 f2 => patternless f1 /\ patternless f2
        | ImpliesI f1 f2 => patternless f1 /\ patternless f2
        | ExistsI fb => patternless fb
        | HasSortI s t => True
        | PatternI t => False
    end.
  End BaseF.

  Module BaseM <: Model Base.
    Export Base.

    Definition M := sigT sort_sem.

    Fixpoint opapply result args (vals : list (option M)) : optype args result -> option M :=
      match args as args, vals return optype args result -> option M with
        | nil, nil => fun f => Some (existT sort_sem result f)
        | a :: args, Some (existT vsort vval) :: vals =>
          match sort_dec a vsort with
            | left aeqv =>
              match aeqv in _ = vsort return sort_sem vsort -> optype (a :: args) result -> option M with
                | refl_equal => fun x f => opapply result args vals (f x)
              end vval
            | right neq => fun _ => None
          end
        | a :: args, None :: vals => fun _ => None
        | nil, _ :: _ => fun _ => None
        | a :: args, nil => fun _ => None
      end.

    Definition lapply : Label -> list (option M) -> option M :=
      fun l vals =>
      opapply
        (projT1 (projT2 (label_sem l)))
        (projT1 (label_sem l))
        vals
        (projT2 (projT2 (label_sem l))).

    Definition Valuation := PositiveMap.t (sigT sort_sem).
    Definition UpdateV env v (x : sigT sort_sem) := PositiveMap.add (Var_var v) x env.

    Fixpoint value' (defs : Valuation) (bound : list (sigT sort_sem)) (t : Term TVar)
      : option (sigT sort_sem) :=
      match t with
        | TMVar v =>
          match v with
            | VFree p => PositiveMap.find p defs
            | VBound ix => nth_error bound ix
          end
        | TApp l ts => lapply l (map (value' defs bound) ts)
      end.

    Lemma value'_inTerm (defs : Valuation) (bound : list M) (t : Term positive) :
      value' defs bound (inTerm t) = value' defs nil (inTerm t).
    Proof.
      induction t using term_ind with
        (Ps := fun ts => map (value' defs bound) (map inTerm ts)
          = map (value' defs nil) (map inTerm ts));
      simpl; fold inTerm; congruence.
    Qed.

    Definition value defs t := value' defs nil (inTerm t).

    Definition Compose (env : Valuation) (subst : Substitution) : Valuation :=
      PositiveMap._map2 (fun val repl =>
        match repl with
          | None => val
          | Some t => value env t
        end) env subst.

    Lemma compose_lookup : forall p defs subst,
      PositiveMap.find p (Compose defs subst) =
      match PositiveMap.find p subst with
        | None => PositiveMap.find p defs
        | Some t => value defs t
      end.
    unfold Compose. intros.
    rewrite PositiveMap.gmap2; reflexivity.
    Qed.

    Lemma compose_value : forall defs bound subst t,
      value' defs bound (Apply' subst t) = value' (Compose defs subst) bound t.
    intros.
    induction t as [v| | |] using term_ind with
      (Ps := fun ts =>
        map (value' defs bound) (map (Apply' subst) ts) =
        map (value' (Compose defs subst) bound) ts);
    (* all cases but bound vars are trivial *)
    [destruct v|..];
      [|unfold Apply' in * |- *; simpl; congruence ..].

    unfold Apply', GenericLang.app_var, inTerm, app_var; simpl.
    rewrite compose_lookup.
    destruct (PositiveMap.find p subst).
    simpl in * |- *. fold inTerm.

    rewrite value'_inTerm. reflexivity.
    reflexivity.
    Qed.

  End BaseM.

  Module BaseS <: Satisfaction Base BaseM BaseF.
  Export Base BaseM BaseF.

  Fixpoint Satisfies' (gamma : M) (rho : Valuation ) (bound : list M) (f : Formula) : Prop :=
    match f with
      | EqualsI t1 t2 => SomeEqual _ (value' rho bound t1) (value' rho bound t2)
      | AndI f1 f2 => Satisfies' gamma rho bound f1 /\ Satisfies' gamma rho bound f2
      | OrI f1 f2 => Satisfies' gamma rho bound f1 \/ Satisfies' gamma rho bound f2
      | ImpliesI f1 f2 => Satisfies' gamma rho bound f1 -> Satisfies' gamma rho bound f2
      | ExistsI fb => exists t, Satisfies' gamma rho (t :: bound) fb
      | HasSortI s t => exists v, value' rho bound t = Some (existT _ s v)
      | PatternI t => Some gamma = value' rho bound t
    end.

  Definition Satisfies (gamma : M) (rho : Valuation) (f : Formula) : Prop :=
    Satisfies' gamma rho nil f.

  Lemma SatApply : forall rho f subst gamma,
    Satisfies gamma rho (ApplyF subst f) <->
    Satisfies gamma (Compose rho subst) f.
  unfold Satisfies. generalize (@nil M) as bound. intros; revert bound.
  induction f;
    solve[simpl;try setoid_rewrite <- compose_value;
      (repeat match goal with
    | [ IH : forall bound, _ <-> _ |- _] =>
      setoid_rewrite IH; clear IH
        end); reflexivity].
  Qed.

  Lemma patternless_sat : forall f, patternless f ->
    forall gamma gamma' rho,
      Satisfies gamma rho f -> Satisfies gamma' rho f.

    unfold Satisfies; intros until rho; generalize (@nil M) as bound;
      revert gamma gamma'; induction f; simpl in * |- *; intros;
    try solve[intuition eauto].

    destruct H0 as [t Hsat].
    exists t. apply IHf with gamma; assumption.
  Qed.

  Lemma notFree_val : forall rho bound x t0 t,
    varpred (notFreeTV (Var_var x)) t ->
    value' rho bound t =
    value' (UpdateV rho x t0) bound t.
  Proof.
    intros.
    induction t using term_ind with (Ps := fun ts =>
      (fix goods (ts0 : list (Term TVar)) : Prop :=
        match ts0 with
          | nil => True
          | t :: ts1 => varpred (notFreeTV (Var_var x)) t /\ goods ts1
        end) ts ->
      map (value' rho bound) ts =
        map (value' (UpdateV rho x t0) bound) ts)
    ; simpl.

    destruct x as [[] []]; destruct v; simpl.
    unfold UpdateV; simpl.
    simpl in H; rewrite PositiveMap.gso;congruence.
    reflexivity.
    simpl in H; rewrite IHt.
    reflexivity.
    assumption.
    reflexivity.

    destruct H.
    specialize (IHt H).
    specialize (IHt0 H0).
    congruence.
  Qed.

  Lemma notFree_sat : forall x f,
    notFree x f ->
    forall gamma rho t,
      Satisfies gamma rho f
      <-> Satisfies gamma (UpdateV rho x t) f.
  Proof.
    unfold Satisfies; generalize (@nil M) as bound; intros; revert bound.
    induction f; simpl; intros; simpl in H; try destruct H.

    setoid_rewrite <- notFree_val;[reflexivity|assumption..].

    rewrite (IHf1 H), (IHf2 H0); reflexivity.
    rewrite (IHf1 H), (IHf2 H0); reflexivity.
    rewrite (IHf1 H), (IHf2 H0); reflexivity.

    setoid_rewrite (fun t => IHf H (t :: bound));reflexivity.

    rewrite (notFree_val rho bound x t t0 H); reflexivity.

    setoid_rewrite <- notFree_val;[reflexivity|assumption..].
  Qed.

  Lemma SatEquals : forall (rho : Valuation) (t t' : T) (gamma : M),
    SomeEqual _ (value rho t) (value rho t')
    <->
    Satisfies gamma rho (Equals t t').
  Proof.
    reflexivity.
  Qed.

  Lemma term_bound : forall (t : Term TVar)
    (rho : Valuation) (x : Var) (v : M) (boundl boundr : list M),
    value' (UpdateV rho x v) (boundl ++ boundr) t
    = value' rho (boundl ++ v :: boundr) (bindTerm (Var_var x) (length boundl) t).
  Proof.
    intros.
    induction t using term_ind with
      (Ps := fun ts => map (value' (UpdateV rho x v) (boundl ++ boundr)) ts 
        = map (value' rho (boundl ++ v :: boundr)) 
            (map (bindTerm (Var_var x) (length boundl)) ts));
      simpl; try congruence.

    (* variable case*)
    destruct v0; simpl.
    
    (* named variable *)
      unfold UpdateV; destruct x as [[] []]; simpl.
      destruct (positive_eq_dec v0 p).
      (* equal x *)
      subst. rewrite PositiveMap.gss.
      induction boundl.
      reflexivity. assumption.
      (* not equal *)
      apply PositiveMap.gso; congruence.

    (* bound variable *)
    revert ix.
    induction boundl.
      reflexivity.
      destruct ix.
        reflexivity.
        simpl. rewrite IHboundl.
        destruct (Compare_dec.leb (length boundl) ix); reflexivity.
 
    (* apply case *)
    rewrite IHt. reflexivity.
  Qed.

  Lemma SatBound : forall (phi : Formula) (rho : Valuation) (x : Var)
    (boundl boundr : list M) (gamma : M) (t : M),
    Satisfies' gamma (UpdateV rho x t) (boundl++boundr) phi <->
    Satisfies' gamma rho (boundl ++ t :: boundr) (bindAs (Var_var x) (length boundl) phi).
  Proof.
    intros; revert boundl; induction phi; simpl; intros.

    setoid_rewrite term_bound; reflexivity.

    repeat match goal with
             [ H : forall (boundl : list M), _ |- _] =>
             setoid_rewrite H;clear H
           end; reflexivity.
    repeat match goal with
             [ H : forall (boundl : list M), _ |- _] =>
             setoid_rewrite H;clear H
           end; reflexivity.
    repeat match goal with
             [ H : forall (boundl : list M), _ |- _] =>
             setoid_rewrite H;clear H
           end; reflexivity.

    pose proof (fun t0 => IHphi (t0 :: boundl)).
    simpl in H. setoid_rewrite H. reflexivity.

    setoid_rewrite term_bound; reflexivity.
    setoid_rewrite term_bound; reflexivity.
  Qed.
    
  Lemma SatExists : forall (rho : Valuation) (x : Var) (phi : Formula) (gamma : M),
    (exists t : M, Satisfies gamma (UpdateV rho x t) phi)
    <->
    Satisfies gamma rho (Exists x phi).
  Proof.
    unfold Satisfies; simpl; generalize (@nil M) as bound; intros; revert rho x bound gamma.
    intros. setoid_rewrite (SatBound phi rho x nil bound gamma). reflexivity.
  Qed.

  Lemma SatAnd : forall (rho : Valuation) (phi phi' : Formula) (gamma : M),
    (Satisfies gamma rho phi /\ Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (And phi phi').
  Proof.
    reflexivity.
  Qed.

  Lemma SatOr : forall (rho : Valuation) (phi phi' : Formula) (gamma : M),
    (Satisfies gamma rho phi \/ Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (Or phi phi').
  Proof.
    reflexivity.
  Qed.
    
  Lemma SatImplies : forall (rho : Valuation) (phi phi' : Formula) (gamma : M),
    (Satisfies gamma rho phi -> Satisfies gamma rho phi')
    <->
    Satisfies gamma rho (Implies phi phi').
  Proof.
    reflexivity.
  Qed.

  Lemma SatPattern : forall (rho : Valuation) (t : T) (gamma : M),
    (Some gamma = value rho t)
    <->
    Satisfies gamma rho (Pattern t).
  Proof.
    reflexivity.
  Qed.

  Definition Valid phi :=
    forall gamma : M, forall rho : Valuation,
      Satisfies gamma rho phi.

  End BaseS.
End GenericLang.

Module LabelTest <: Labels.
  Inductive SortI := snat.
  Definition Sort := SortI.
  Definition sort_sem (s : Sort) := nat.

  Lemma sort_dec : forall (x y:Sort), {x=y}+{x<>y}.
    decide equality.
  Qed.

  Fixpoint optype args result :=
    match args with
      | nil => sort_sem result
      | arg :: args => sort_sem arg -> optype args result
    end.

  Inductive LabelI : Set := zed.
  Definition Label := LabelI.
  Definition label_sem (l : Label) :
    {args : list Sort & {result : Sort & optype args result}} :=
    existT _ nil (existT _ snat 0).
End LabelTest.

Module GenTest := GenericLang LabelTest.