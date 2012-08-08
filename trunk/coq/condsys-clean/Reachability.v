Require Import Terms.
Require Import Model.
Require Import Patterns.
Require Import Satisfaction.
Require Import Closure.
Require Import Relation_Definitions.
Require Import List.

Module Type ObjectLanguage.
  Declare Module Export Base : Terms.
  Declare Module Export BaseM : Model Base.
  Declare Module Export BaseP : Patterns Base.
  Declare Module Export BaseS : Satisfaction Base BaseM BaseP.
End ObjectLanguage.

Module Type Reachability (Export Base : ObjectLanguage).

  Definition SimpleRule := (Pattern * Pattern)%type.
  
  Definition SimpleSystem := list SimpleRule.

  Definition CondRule := (SimpleRule * SimpleSystem)%type.
  
  Definition CondSystem := CondRule -> Prop.

  Fixpoint mapFst (l : list SimpleRule) :=
    match l with
      | nil => nil
      | cons hd tl =>
        cons (fst hd) (mapFst tl)
    end.

  Fixpoint mapSnd (l : list SimpleRule) :=
    match l with
      | nil => nil
      | cons hd tl =>
        cons (snd hd) (mapFst tl)
    end.

  Inductive InTSList (R : relation M) : list M -> list M -> Prop :=
  | InTSListNil :
    InTSList R nil nil
  | InTSListCons :
    forall hd hd' tl tl',
      R hd hd' ->
      InTSList R tl tl' ->
      InTSList R (cons hd tl) (cons hd' tl').

  Inductive SatisfiesList : list M -> Valuation -> list Pattern -> Prop :=
  | SatisfiesListNil :
    forall rho,
      SatisfiesList nil rho nil
  | SatisfiesListCons :
    forall gamma gammaTail phi phiTail rho,
      Satisfies gamma rho phi ->
      SatisfiesList gammaTail rho phiTail ->
      SatisfiesList (cons gamma gammaTail) rho (cons phi phiTail).

  Inductive TS (csys : CondSystem) : relation M :=
    | TSIntro : forall (rule : CondRule),
      csys rule ->
      forall (rho : Valuation),
        forall gamma gamma',
          Satisfies gamma rho (fst (fst rule)) ->
          Satisfies gamma' rho (snd (fst rule)) ->
          (forall gammaList : list M,
            SatisfiesList gammaList rho (mapFst (snd rule)) ->
            exists gammaList' : list M,
              InTSList (clos _ (TS csys) false) gammaList gammaList') ->
          TS csys gamma gamma'.

  Definition TSStar (csys : CondSystem) : relation M :=
    clos _ (TS csys) false.

  Parameter S : CondSystem.

  Definition RhoStronglyValid (rho : Valuation) (srule : SimpleRule) :=
    forall gamma,
      Satisfies gamma rho (fst srule) ->
      exists gamma',
        TSStar S gamma gamma' /\
        Satisfies gamma' rho (snd srule).

  Definition StronglyValid (srule : SimpleRule) :=
    forall rho,
      RhoStronglyValid rho srule.
  
  Inductive IsSuffix { A : Type } : list A -> list A -> Prop :=
  | here :
    forall slist,
      IsSuffix slist slist
  | next :
    forall slist blist bhead,
      IsSuffix slist blist ->
      IsSuffix slist (bhead :: blist).
      
  Notation "x 'SuffixOf' y" := (IsSuffix x y) (at level 60, right associativity).
  
  Definition TerminationDependence (csys : CondSystem) (gamma gamma' : M) : Prop :=
    (TSStar csys) gamma gamma' \/
    exists rule,
      (csys rule /\
        exists rho,
          exists rest : SimpleSystem,
            exists irule : SimpleRule,
              (cons irule rest) SuffixOf (snd rule) /\
              Satisfies gamma rho (fst (fst rule)) /\
              List.Forall (fun rule => RhoStronglyValid rho rule) rest /\
              Satisfies gamma' rho (fst irule)).

  Definition Prec csys gamma gamma' :=
    (clos _ (TerminationDependence csys) true) gamma' gamma.

  Definition Terminates (csys : CondSystem) gamma :=
    Acc (Prec csys) gamma.

  Definition TerminatesPattern (csys : CondSystem) phi :=
    forall gamma rho,
      Satisfies gamma rho phi ->
      Terminates csys gamma.

  Definition WeaklyWD (rule : CondRule) :=
    WeaklyWDPattern (snd (fst rule)) /\
    List.Forall WeaklyWDPattern (mapFst (snd rule)).

  Definition WD (rule : CondRule) :=
    WDPattern (snd (fst rule)) /\
    List.Forall WDPattern (mapFst (snd rule)).

  Definition WeaklyWDSystem (csys : CondSystem) :=
    forall rule,
      csys rule ->
      WeaklyWD rule.
  
  Definition WDSystem (csys : CondSystem) :=
    forall rule,
      csys rule ->
      WD rule.

  Definition GR : relation M := TSStar S.

  Notation "x 'Succ' y" := (TerminationDependence S x y) (at level 60).

  Notation "y 'SuccEq' yy" := (clos M (TerminationDependence S) false y yy) (at level 60).

  Definition GoesTo strict gamma gamma' := clos M (TS S) strict gamma gamma'.

  Definition RhoValid (srule : SimpleRule) (rho : Valuation) :=
    forall gamma,
      Satisfies gamma rho (fst srule) ->
      Terminates S gamma ->
      exists gamma',
        (Satisfies gamma' rho (snd srule) /\
          GoesTo false gamma gamma').

  Definition Valid (srule : SimpleRule) :=
    forall rho,
      RhoValid srule rho.
  
End Reachability.
