Require Import Reachability.

Module Type ProofSystem (Base : ObjectLanguage)
  (BaseR : Reachability Base).

  Export Base.
  Export BaseR.

  Definition IsEmpty (ssys : SimpleSystem) := ssys = nil.

  Definition ssysEmpty : SimpleSystem := nil.
  
  Definition cruleOfsrule (srule : SimpleRule) : CondRule :=
    (srule, ssysEmpty).

  Definition csysOfssys (ssys : SimpleSystem) : CondSystem :=
    fun crule =>
      exists srule,
        (List.In srule ssys /\
          crule = cruleOfsrule srule).

  Definition csysUnion (csys1 : CondSystem) (csys2 : CondSystem) :=
  fun crule => csys1 crule \/ csys2 crule.

  Definition ssysCons phi phi' ssys : SimpleSystem :=
    cons (phi, phi') ssys.

  Definition ssysUnion ssys1 ssys2 : SimpleSystem :=
    app ssys1 ssys2.
  
  Inductive PS : SimpleSystem -> SimpleSystem -> Pattern -> Pattern -> Prop :=
  | ps_axiom_S : 
    forall A C psi crule,
      S crule ->
      structureless psi ->
      (forall srule,
        List.In srule (snd crule) ->
        PS (ssysUnion A C) ssysEmpty (And (fst srule) psi) (snd srule)) ->
      PS A C (And (fst (fst crule)) psi) (And (snd (fst crule)) psi)
  | ps_axiom_A :
    forall (A : SimpleSystem) (C : SimpleSystem) psi srule,
      List.In srule A ->
      structureless psi ->
      PS A C (And (fst srule) psi) (And (snd srule) psi)
  | ps_refl :
    forall A phi,
      PS A ssysEmpty phi phi
  | ps_trans :
    forall A C phi1 phi2 phi3,
      PS A C phi1 phi2 ->
      PS (ssysUnion A C) ssysEmpty phi2 phi3 ->
      PS A C phi1 phi3
  | ps_conseq :
    forall A C phi1 phi1' phi2 phi2',
      ValidPattern (Implies phi1 phi1') ->
      PS A C phi1' phi2' ->
      ValidPattern (Implies phi2' phi2) ->
      PS A C phi1 phi2
  | ps_case :
    forall A C phi1 phi phi2,
      PS A C phi1 phi ->
      PS A C phi2 phi ->
      PS A C (Or phi1 phi2) phi
  | ps_abstr :
    forall A C X phi phi',
      PS A C phi phi' ->
      notFree X phi' ->
      PS A C (Exists X phi) phi'
  | ps_circ :
    forall A C phi phi',
      PS A (ssysCons phi phi' C) phi phi' ->
      PS A C phi phi'.  

End ProofSystem.
