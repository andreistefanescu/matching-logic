Require Import ZArith.
Require Import FMapPositive.
Require Import List.

Add LoadPath "../../ml_proof".
Require Import matchingl.
Require Import generic.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Require Import domains.

Inductive Sort : Set :=
  | sId | sVal | sBool | sStore
  | sExp | sBExp | sStmt
  | scfg | sscfg
  | sCtxt (s1 s2 : Sort)
  | skcfg | sfreezer | skitem | sklist.
Fixpoint sort_sem s : Set :=
  match s with
  | sId => Var
  | sVal => Z
  | sBool => bool
  | sStore => Store
  | sExp => Exp 
  | sBExp => BExp 
  | sStmt => Stmt
  | scfg => cfg
  | sscfg => sosCfg
  | sCtxt s1 s2 => ctxt (sort_sem s1) (sort_sem s2)
  | skcfg => kcfg
  | sfreezer => freezer
  | skitem => kitem
  | sklist => list kitem
  end.
Ltac sort_fold t cont :=
  match t with
    | Var => cont sId
    | Z => cont sVal
    | bool => cont sBool
    | Store => cont sStore
    | Exp => cont sExp
    | BExp => cont sBExp
    | Stmt => cont sStmt
    | cfg => cont scfg
    | sosCfg => cont sscfg
    | ctxt ?s1 ?s2 =>
      sort_fold s1 ltac:(fun s1t =>
        sort_fold s2 ltac:(fun s2t =>
          let rt := constr:(sCtxt s1t s2t) in
            cont rt))
    | kcfg => cont skcfg
    | freezer => cont sfreezer
    | kitem => cont skitem
    | list kitem => cont sklist
  end.
Ltac optype_fold t cont :=
  match t with
    | (?a -> ?b) =>
      sort_fold a ltac:(fun aterm =>
        optype_fold b ltac:(fun args' rest =>
          let argst := constr:(@cons Sort aterm args') in
          cont argst rest))
    | (?r) => sort_fold r ltac:(fun rt => cont (@nil Sort) rt)
  end.

Definition sort_dec : forall (x y:Sort), {x=y}+{x<>y} :=
fun x y : Sort =>
let H :=
  Sort_rec (fun x0 : Sort => forall y0 : Sort, {x0 = y0} + {x0 <> y0})
    (fun y0 : Sort =>
     match y0 as s return ({sId = s} + {sId <> s}) with
     | sId => left (sId <> sId) (eq_refl sId)
     | sVal =>
         right (sId = sVal)
           (fun H : sId = sVal =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (sId = sBool)
           (fun H : sId = sBool =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (sId = sStore)
           (fun H : sId = sStore =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (sId = sExp)
           (fun H : sId = sExp =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (sId = sBExp)
           (fun H : sId = sBExp =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (sId = sStmt)
           (fun H : sId = sStmt =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sId = scfg)
           (fun H : sId = scfg =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sId = sscfg)
           (fun H : sId = sscfg =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sId = sCtxt s1 s2)
           (fun H : sId = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sId = skcfg)
           (fun H : sId = skcfg =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sId = sfreezer)
           (fun H : sId = sfreezer =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sId = skitem)
           (fun H : sId = skitem =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sId = sklist)
           (fun H : sId = sklist =>
            let H0 :=
              eq_ind sId
                (fun e : Sort =>
                 match e with
                 | sId => True
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sVal = s} + {sVal <> s}) with
     | sId =>
         right (sVal = sId)
           (fun H : sVal = sId =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal => left (sVal <> sVal) (eq_refl sVal)
     | sBool =>
         right (sVal = sBool)
           (fun H : sVal = sBool =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (sVal = sStore)
           (fun H : sVal = sStore =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (sVal = sExp)
           (fun H : sVal = sExp =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (sVal = sBExp)
           (fun H : sVal = sBExp =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (sVal = sStmt)
           (fun H : sVal = sStmt =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sVal = scfg)
           (fun H : sVal = scfg =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sVal = sscfg)
           (fun H : sVal = sscfg =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sVal = sCtxt s1 s2)
           (fun H : sVal = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sVal = skcfg)
           (fun H : sVal = skcfg =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sVal = sfreezer)
           (fun H : sVal = sfreezer =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sVal = skitem)
           (fun H : sVal = skitem =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sVal = sklist)
           (fun H : sVal = sklist =>
            let H0 :=
              eq_ind sVal
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => True
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sBool = s} + {sBool <> s}) with
     | sId =>
         right (sBool = sId)
           (fun H : sBool = sId =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (sBool = sVal)
           (fun H : sBool = sVal =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool => left (sBool <> sBool) (eq_refl sBool)
     | sStore =>
         right (sBool = sStore)
           (fun H : sBool = sStore =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (sBool = sExp)
           (fun H : sBool = sExp =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (sBool = sBExp)
           (fun H : sBool = sBExp =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (sBool = sStmt)
           (fun H : sBool = sStmt =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sBool = scfg)
           (fun H : sBool = scfg =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sBool = sscfg)
           (fun H : sBool = sscfg =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sBool = sCtxt s1 s2)
           (fun H : sBool = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sBool = skcfg)
           (fun H : sBool = skcfg =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sBool = sfreezer)
           (fun H : sBool = sfreezer =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sBool = skitem)
           (fun H : sBool = skitem =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sBool = sklist)
           (fun H : sBool = sklist =>
            let H0 :=
              eq_ind sBool
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => True
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sStore = s} + {sStore <> s}) with
     | sId =>
         right (sStore = sId)
           (fun H : sStore = sId =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (sStore = sVal)
           (fun H : sStore = sVal =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (sStore = sBool)
           (fun H : sStore = sBool =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore => left (sStore <> sStore) (eq_refl sStore)
     | sExp =>
         right (sStore = sExp)
           (fun H : sStore = sExp =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (sStore = sBExp)
           (fun H : sStore = sBExp =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (sStore = sStmt)
           (fun H : sStore = sStmt =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sStore = scfg)
           (fun H : sStore = scfg =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sStore = sscfg)
           (fun H : sStore = sscfg =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sStore = sCtxt s1 s2)
           (fun H : sStore = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sStore = skcfg)
           (fun H : sStore = skcfg =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sStore = sfreezer)
           (fun H : sStore = sfreezer =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sStore = skitem)
           (fun H : sStore = skitem =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sStore = sklist)
           (fun H : sStore = sklist =>
            let H0 :=
              eq_ind sStore
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => True
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sExp = s} + {sExp <> s}) with
     | sId =>
         right (sExp = sId)
           (fun H : sExp = sId =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (sExp = sVal)
           (fun H : sExp = sVal =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (sExp = sBool)
           (fun H : sExp = sBool =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (sExp = sStore)
           (fun H : sExp = sStore =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp => left (sExp <> sExp) (eq_refl sExp)
     | sBExp =>
         right (sExp = sBExp)
           (fun H : sExp = sBExp =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (sExp = sStmt)
           (fun H : sExp = sStmt =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sExp = scfg)
           (fun H : sExp = scfg =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sExp = sscfg)
           (fun H : sExp = sscfg =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sExp = sCtxt s1 s2)
           (fun H : sExp = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sExp = skcfg)
           (fun H : sExp = skcfg =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sExp = sfreezer)
           (fun H : sExp = sfreezer =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sExp = skitem)
           (fun H : sExp = skitem =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sExp = sklist)
           (fun H : sExp = sklist =>
            let H0 :=
              eq_ind sExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => True
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sBExp = s} + {sBExp <> s}) with
     | sId =>
         right (sBExp = sId)
           (fun H : sBExp = sId =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (sBExp = sVal)
           (fun H : sBExp = sVal =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (sBExp = sBool)
           (fun H : sBExp = sBool =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (sBExp = sStore)
           (fun H : sBExp = sStore =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (sBExp = sExp)
           (fun H : sBExp = sExp =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp => left (sBExp <> sBExp) (eq_refl sBExp)
     | sStmt =>
         right (sBExp = sStmt)
           (fun H : sBExp = sStmt =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sBExp = scfg)
           (fun H : sBExp = scfg =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sBExp = sscfg)
           (fun H : sBExp = sscfg =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sBExp = sCtxt s1 s2)
           (fun H : sBExp = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sBExp = skcfg)
           (fun H : sBExp = skcfg =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sBExp = sfreezer)
           (fun H : sBExp = sfreezer =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sBExp = skitem)
           (fun H : sBExp = skitem =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sBExp = sklist)
           (fun H : sBExp = sklist =>
            let H0 :=
              eq_ind sBExp
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => True
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sStmt = s} + {sStmt <> s}) with
     | sId =>
         right (sStmt = sId)
           (fun H : sStmt = sId =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (sStmt = sVal)
           (fun H : sStmt = sVal =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (sStmt = sBool)
           (fun H : sStmt = sBool =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (sStmt = sStore)
           (fun H : sStmt = sStore =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (sStmt = sExp)
           (fun H : sStmt = sExp =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (sStmt = sBExp)
           (fun H : sStmt = sBExp =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt => left (sStmt <> sStmt) (eq_refl sStmt)
     | scfg =>
         right (sStmt = scfg)
           (fun H : sStmt = scfg =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sStmt = sscfg)
           (fun H : sStmt = sscfg =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sStmt = sCtxt s1 s2)
           (fun H : sStmt = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sStmt = skcfg)
           (fun H : sStmt = skcfg =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sStmt = sfreezer)
           (fun H : sStmt = sfreezer =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sStmt = skitem)
           (fun H : sStmt = skitem =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sStmt = sklist)
           (fun H : sStmt = sklist =>
            let H0 :=
              eq_ind sStmt
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => True
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({scfg = s} + {scfg <> s}) with
     | sId =>
         right (scfg = sId)
           (fun H : scfg = sId =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (scfg = sVal)
           (fun H : scfg = sVal =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (scfg = sBool)
           (fun H : scfg = sBool =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (scfg = sStore)
           (fun H : scfg = sStore =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (scfg = sExp)
           (fun H : scfg = sExp =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (scfg = sBExp)
           (fun H : scfg = sBExp =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (scfg = sStmt)
           (fun H : scfg = sStmt =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg => left (scfg <> scfg) (eq_refl scfg)
     | sscfg =>
         right (scfg = sscfg)
           (fun H : scfg = sscfg =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (scfg = sCtxt s1 s2)
           (fun H : scfg = sCtxt s1 s2 =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (scfg = skcfg)
           (fun H : scfg = skcfg =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (scfg = sfreezer)
           (fun H : scfg = sfreezer =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (scfg = skitem)
           (fun H : scfg = skitem =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (scfg = sklist)
           (fun H : scfg = sklist =>
            let H0 :=
              eq_ind scfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => True
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sscfg = s} + {sscfg <> s}) with
     | sId =>
         right (sscfg = sId)
           (fun H : sscfg = sId =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (sscfg = sVal)
           (fun H : sscfg = sVal =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (sscfg = sBool)
           (fun H : sscfg = sBool =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (sscfg = sStore)
           (fun H : sscfg = sStore =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (sscfg = sExp)
           (fun H : sscfg = sExp =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (sscfg = sBExp)
           (fun H : sscfg = sBExp =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (sscfg = sStmt)
           (fun H : sscfg = sStmt =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sscfg = scfg)
           (fun H : sscfg = scfg =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg => left (sscfg <> sscfg) (eq_refl sscfg)
     | sCtxt s1 s2 =>
         right (sscfg = sCtxt s1 s2)
           (fun H : sscfg = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sscfg = skcfg)
           (fun H : sscfg = skcfg =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sscfg = sfreezer)
           (fun H : sscfg = sfreezer =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sscfg = skitem)
           (fun H : sscfg = skitem =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sscfg = sklist)
           (fun H : sscfg = sklist =>
            let H0 :=
              eq_ind sscfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => True
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun (s1 : Sort) (H : forall y0 : Sort, {s1 = y0} + {s1 <> y0})
       (s2 : Sort) (H0 : forall y0 : Sort, {s2 = y0} + {s2 <> y0})
       (y0 : Sort) =>
     match y0 as s return ({sCtxt s1 s2 = s} + {sCtxt s1 s2 <> s}) with
     | sId =>
         right (sCtxt s1 s2 = sId)
           (fun H1 : sCtxt s1 s2 = sId =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H1 in
            False_ind False H2)
     | sVal =>
         right (sCtxt s1 s2 = sVal)
           (fun H1 : sCtxt s1 s2 = sVal =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H1 in
            False_ind False H2)
     | sBool =>
         right (sCtxt s1 s2 = sBool)
           (fun H1 : sCtxt s1 s2 = sBool =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H1 in
            False_ind False H2)
     | sStore =>
         right (sCtxt s1 s2 = sStore)
           (fun H1 : sCtxt s1 s2 = sStore =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H1 in
            False_ind False H2)
     | sExp =>
         right (sCtxt s1 s2 = sExp)
           (fun H1 : sCtxt s1 s2 = sExp =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H1 in
            False_ind False H2)
     | sBExp =>
         right (sCtxt s1 s2 = sBExp)
           (fun H1 : sCtxt s1 s2 = sBExp =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H1 in
            False_ind False H2)
     | sStmt =>
         right (sCtxt s1 s2 = sStmt)
           (fun H1 : sCtxt s1 s2 = sStmt =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H1 in
            False_ind False H2)
     | scfg =>
         right (sCtxt s1 s2 = scfg)
           (fun H1 : sCtxt s1 s2 = scfg =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H1 in
            False_ind False H2)
     | sscfg =>
         right (sCtxt s1 s2 = sscfg)
           (fun H1 : sCtxt s1 s2 = sscfg =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H1 in
            False_ind False H2)
     | sCtxt s0 s3 =>
         sumbool_rec
           (fun _ : {s1 = s0} + {s1 <> s0} =>
            {sCtxt s1 s2 = sCtxt s0 s3} + {sCtxt s1 s2 <> sCtxt s0 s3})
           (fun a : s1 = s0 =>
            eq_rec_r
              (fun s4 : Sort =>
               {sCtxt s4 s2 = sCtxt s0 s3} + {sCtxt s4 s2 <> sCtxt s0 s3})
              (sumbool_rec
                 (fun _ : {s2 = s3} + {s2 <> s3} =>
                  {sCtxt s0 s2 = sCtxt s0 s3} + {sCtxt s0 s2 <> sCtxt s0 s3})
                 (fun a0 : s2 = s3 =>
                  eq_rec_r
                    (fun s4 : Sort =>
                     {sCtxt s0 s4 = sCtxt s0 s3} +
                     {sCtxt s0 s4 <> sCtxt s0 s3})
                    (left (sCtxt s0 s3 <> sCtxt s0 s3)
                       (eq_refl (sCtxt s0 s3))) a0)
                 (fun diseq : s2 <> s3 =>
                  right (sCtxt s0 s2 = sCtxt s0 s3)
                    (fun absurd : sCtxt s0 s2 = sCtxt s0 s3 =>
                     diseq
                       (let H1 :=
                          f_equal
                            (fun e : Sort =>
                             match e with
                             | sId => s2
                             | sVal => s2
                             | sBool => s2
                             | sStore => s2
                             | sExp => s2
                             | sBExp => s2
                             | sStmt => s2
                             | scfg => s2
                             | sscfg => s2
                             | sCtxt _ s5 => s5
                             | skcfg => s2
                             | sfreezer => s2
                             | skitem => s2
                             | sklist => s2
                             end) absurd in
                        H1))) (H0 s3)) a)
           (fun diseq : s1 <> s0 =>
            right (sCtxt s1 s2 = sCtxt s0 s3)
              (fun absurd : sCtxt s1 s2 = sCtxt s0 s3 =>
               diseq
                 (let H1 :=
                    f_equal
                      (fun e : Sort =>
                       match e with
                       | sId => s1
                       | sVal => s1
                       | sBool => s1
                       | sStore => s1
                       | sExp => s1
                       | sBExp => s1
                       | sStmt => s1
                       | scfg => s1
                       | sscfg => s1
                       | sCtxt s4 _ => s4
                       | skcfg => s1
                       | sfreezer => s1
                       | skitem => s1
                       | sklist => s1
                       end) absurd in
                  (let H2 :=
                     f_equal
                       (fun e : Sort =>
                        match e with
                        | sId => s2
                        | sVal => s2
                        | sBool => s2
                        | sStore => s2
                        | sExp => s2
                        | sBExp => s2
                        | sStmt => s2
                        | scfg => s2
                        | sscfg => s2
                        | sCtxt _ s5 => s5
                        | skcfg => s2
                        | sfreezer => s2
                        | skitem => s2
                        | sklist => s2
                        end) absurd in
                   fun H3 : s1 = s0 => H3) H1))) (H s0)
     | skcfg =>
         right (sCtxt s1 s2 = skcfg)
           (fun H1 : sCtxt s1 s2 = skcfg =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skcfg H1 in
            False_ind False H2)
     | sfreezer =>
         right (sCtxt s1 s2 = sfreezer)
           (fun H1 : sCtxt s1 s2 = sfreezer =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H1 in
            False_ind False H2)
     | skitem =>
         right (sCtxt s1 s2 = skitem)
           (fun H1 : sCtxt s1 s2 = skitem =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H1 in
            False_ind False H2)
     | sklist =>
         right (sCtxt s1 s2 = sklist)
           (fun H1 : sCtxt s1 s2 = sklist =>
            let H2 :=
              eq_ind (sCtxt s1 s2)
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => True
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H1 in
            False_ind False H2)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({skcfg = s} + {skcfg <> s}) with
     | sId =>
         right (skcfg = sId)
           (fun H : skcfg = sId =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (skcfg = sVal)
           (fun H : skcfg = sVal =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (skcfg = sBool)
           (fun H : skcfg = sBool =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (skcfg = sStore)
           (fun H : skcfg = sStore =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (skcfg = sExp)
           (fun H : skcfg = sExp =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (skcfg = sBExp)
           (fun H : skcfg = sBExp =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (skcfg = sStmt)
           (fun H : skcfg = sStmt =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (skcfg = scfg)
           (fun H : skcfg = scfg =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (skcfg = sscfg)
           (fun H : skcfg = sscfg =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (skcfg = sCtxt s1 s2)
           (fun H : skcfg = sCtxt s1 s2 =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg => left (skcfg <> skcfg) (eq_refl skcfg)
     | sfreezer =>
         right (skcfg = sfreezer)
           (fun H : skcfg = sfreezer =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (skcfg = skitem)
           (fun H : skcfg = skitem =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (skcfg = sklist)
           (fun H : skcfg = sklist =>
            let H0 :=
              eq_ind skcfg
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => True
                 | sfreezer => False
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sfreezer = s} + {sfreezer <> s}) with
     | sId =>
         right (sfreezer = sId)
           (fun H : sfreezer = sId =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (sfreezer = sVal)
           (fun H : sfreezer = sVal =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (sfreezer = sBool)
           (fun H : sfreezer = sBool =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (sfreezer = sStore)
           (fun H : sfreezer = sStore =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (sfreezer = sExp)
           (fun H : sfreezer = sExp =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (sfreezer = sBExp)
           (fun H : sfreezer = sBExp =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (sfreezer = sStmt)
           (fun H : sfreezer = sStmt =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sfreezer = scfg)
           (fun H : sfreezer = scfg =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sfreezer = sscfg)
           (fun H : sfreezer = sscfg =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sfreezer = sCtxt s1 s2)
           (fun H : sfreezer = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sfreezer = skcfg)
           (fun H : sfreezer = skcfg =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer => left (sfreezer <> sfreezer) (eq_refl sfreezer)
     | skitem =>
         right (sfreezer = skitem)
           (fun H : sfreezer = skitem =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I skitem H in
            False_ind False H0)
     | sklist =>
         right (sfreezer = sklist)
           (fun H : sfreezer = sklist =>
            let H0 :=
              eq_ind sfreezer
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => True
                 | skitem => False
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({skitem = s} + {skitem <> s}) with
     | sId =>
         right (skitem = sId)
           (fun H : skitem = sId =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (skitem = sVal)
           (fun H : skitem = sVal =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (skitem = sBool)
           (fun H : skitem = sBool =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (skitem = sStore)
           (fun H : skitem = sStore =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (skitem = sExp)
           (fun H : skitem = sExp =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (skitem = sBExp)
           (fun H : skitem = sBExp =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (skitem = sStmt)
           (fun H : skitem = sStmt =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (skitem = scfg)
           (fun H : skitem = scfg =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (skitem = sscfg)
           (fun H : skitem = sscfg =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (skitem = sCtxt s1 s2)
           (fun H : skitem = sCtxt s1 s2 =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (skitem = skcfg)
           (fun H : skitem = skcfg =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (skitem = sfreezer)
           (fun H : skitem = sfreezer =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sfreezer H in
            False_ind False H0)
     | skitem => left (skitem <> skitem) (eq_refl skitem)
     | sklist =>
         right (skitem = sklist)
           (fun H : skitem = sklist =>
            let H0 :=
              eq_ind skitem
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => True
                 | sklist => False
                 end) I sklist H in
            False_ind False H0)
     end)
    (fun y0 : Sort =>
     match y0 as s return ({sklist = s} + {sklist <> s}) with
     | sId =>
         right (sklist = sId)
           (fun H : sklist = sId =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sId H in
            False_ind False H0)
     | sVal =>
         right (sklist = sVal)
           (fun H : sklist = sVal =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sVal H in
            False_ind False H0)
     | sBool =>
         right (sklist = sBool)
           (fun H : sklist = sBool =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sBool H in
            False_ind False H0)
     | sStore =>
         right (sklist = sStore)
           (fun H : sklist = sStore =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sStore H in
            False_ind False H0)
     | sExp =>
         right (sklist = sExp)
           (fun H : sklist = sExp =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sExp H in
            False_ind False H0)
     | sBExp =>
         right (sklist = sBExp)
           (fun H : sklist = sBExp =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sBExp H in
            False_ind False H0)
     | sStmt =>
         right (sklist = sStmt)
           (fun H : sklist = sStmt =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sStmt H in
            False_ind False H0)
     | scfg =>
         right (sklist = scfg)
           (fun H : sklist = scfg =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I scfg H in
            False_ind False H0)
     | sscfg =>
         right (sklist = sscfg)
           (fun H : sklist = sscfg =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sscfg H in
            False_ind False H0)
     | sCtxt s1 s2 =>
         right (sklist = sCtxt s1 s2)
           (fun H : sklist = sCtxt s1 s2 =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I (sCtxt s1 s2) H in
            False_ind False H0)
     | skcfg =>
         right (sklist = skcfg)
           (fun H : sklist = skcfg =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I skcfg H in
            False_ind False H0)
     | sfreezer =>
         right (sklist = sfreezer)
           (fun H : sklist = sfreezer =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I sfreezer H in
            False_ind False H0)
     | skitem =>
         right (sklist = skitem)
           (fun H : sklist = skitem =>
            let H0 :=
              eq_ind sklist
                (fun e : Sort =>
                 match e with
                 | sId => False
                 | sVal => False
                 | sBool => False
                 | sStore => False
                 | sExp => False
                 | sBExp => False
                 | sStmt => False
                 | scfg => False
                 | sscfg => False
                 | sCtxt _ _ => False
                 | skcfg => False
                 | sfreezer => False
                 | skitem => False
                 | sklist => True
                 end) I skitem H in
            False_ind False H0)
     | sklist => left (sklist <> sklist) (eq_refl sklist)
     end) x in
H y.

Inductive Label :=
(* injecting primitives *)
  | LId (i : Var)
  | LVal (i : Z)
  | LBool (b : bool)
  | LStore (s : Store)

  (* operations on Z *)  
  | LPlusZ
  | LDivZ
  | LNez
  | LZleb
  (* operations on bool *)
  | Lnegb
  (* operations on stores *)
  | LLookup
  | LUpdate
  (* value predicates *)
  | LisEVal
  | LisBool
  (* constructors of Exp *)
  | LEVar
  | LECon
  | LEPlus
  | LEDiv
  (* constructors of BExp *)
  | LBCon
  | LBLe
  | LBNot
  | LBAnd
  (* constructors of Stmt *)
  | LSkip
  | LSAssign
  | LSeq
  | LSIf
  | LSWhile
  (* cfg constructor *)
  | LCfg
  (* contexts *)
  | LSCfg
  | LECfg
  | LBCfg
  | LEhole
  | LBhole
  | LShole
  | Lplusl
  | Lplusr
  | Ldivl
  | Ldivr
  | Llel
  | Ller
  | LandlE
  | LandlB
  | Lassigne
  | LseqE
  | LseqB
  | LseqS
  | LifcE
  | LifcB
  | LwhilecE
  | LwhilecB
  | LcfgcE
  | LcfgcB
  | LcfgcS
  | Lcfgc (s : Sort)
  (* pluging a context *)
  | LplugE
  | LplugB
  | LplugS
  (* freezers *)
  | LFplusl
  | LFplusr
  | LFdivl
  | LFdivr
  | LFlel
  | LFler
  | LFandl
  | LFassign
  | LFseq
  | LFif
  (* kitem constructors *)
  | LKExp
  | LKBExp
  | LKStmt
  | LKFreezer
  (* kcfg constructor *)
  | LKCfg
  (* klist constructors *)
  | Lkra
  | Lkdot
  .

Fixpoint optype args result :=
  match args with
    | nil => sort_sem result
    | arg :: args => sort_sem arg -> optype args result
  end.

Set Implicit Arguments.
Definition label (A : Set) (x : A)
  (args : list Sort) (result : Sort)
  (pf : A = optype args result) : {args : list Sort & {result : Sort & optype args result}}.
refine (existT _ args (existT _ result _)).
exact (eq_rec _ (fun t => t) x _ pf).
Defined.

Definition label_sem (l : Label) : {args : list Sort & {result : Sort & optype args result}}.
Ltac give_type :=
fold Val;fold Store;unfold Val;
match goal with
  [|- ?l = ?r] =>
  optype_fold l ltac:(fun args res =>
    change (optype args res = r))
end; reflexivity.
refine (match l with
  | LId i => label i _ _ _
  | LVal i => label i _ _ _
  | LBool b => label b _ _ _
  | LStore s => label s _ _ _

  | Lnegb => label negb _ _ _
  | LNez => label (Zneq_bool 0%Z) _ _ _
  | LZleb => label Zle_bool _ _ _
  | LPlusZ => label Zplus _ _ _
  | LDivZ => label Zdiv _ _ _
  | LLookup => label lookup _ _ _
  | LUpdate => label update _ _ _

  | LisEVal => label isEVal _ _ _
  | LisBool => label isBool _ _ _
  | LEVar => label EVar _ _ _
  | LECon => label ECon _ _ _
  | LEPlus => label EPlus _ _ _
  | LEDiv => label EDiv _ _ _
  | LBCon => label BCon _ _ _
  | LBLe => label BLe _ _ _
  | LBNot => label BNot _ _ _
  | LBAnd => label BAnd _ _ _
  | LSkip => label Skip _ _ _
  | LSAssign => label SAssign _ _ _
  | LSeq => label Seq _ _ _
  | LSIf => label SIf _ _ _
  | LSWhile => label SWhile _ _ _
  | LCfg => label Cfg _ _ _
  | LECfg => label ECfg _ _ _
  | LBCfg => label BCfg _ _ _
  | LSCfg => label SCfg _ _ _
  | LEhole => label (hole Exp) _ _ _
  | LBhole => label (hole BExp) _ _ _
  | LShole => label (hole Stmt) _ _ _
  | Lplusl => label (@plusl Exp) _ _ _
  | Lplusr => label (@plusr Exp) _ _ _
  | Ldivl => label  (@divl Exp) _ _ _
  | Ldivr => label  (@divr Exp) _ _ _
  | Llel => label (@lel Exp) _ _ _
  | Ller => label (@ler Exp) _ _ _
  | LandlE => label (@andl Exp) _ _ _
  | LandlB => label (@andl BExp) _ _ _
  | Lassigne => label (@assigne Exp) _ _ _
  | LseqE => label (@seqc Exp) _ _ _
  | LseqB => label (@seqc BExp) _ _ _
  | LseqS => label (@seqc Stmt) _ _ _
  | LifcE => label (@ifc Exp) _ _ _
  | LifcB => label (@ifc BExp) _ _ _
  | LwhilecE => label (@whilec Exp) _ _ _
  | LwhilecB => label (@whilec BExp) _ _ _
  | LcfgcE => label (@cfgc Exp) _ _ _
  | LcfgcB => label (@cfgc BExp) _ _ _
  | LcfgcS => label (@cfgc Stmt) _ _ _
  | Lcfgc s => (existT _ (sCtxt s sStmt::sStore::nil)
               (existT _ (sCtxt s scfg) (@cfgc _)))
  | LplugE => label (@plug Exp cfg) _ _ _
  | LplugB => label (@plug BExp cfg) _ _ _
  | LplugS => label (@plug Stmt cfg) _ _ _

  | LFplusl => label Fplusl _ _ _
  | LFplusr => label Fplusr _ _ _
  | LFdivl => label Fdivl _ _ _
  | LFdivr => label Fdivr _ _ _
  | LFlel => label Flel _ _ _
  | LFler => label Fler _ _ _
  | LFandl => label Fandl _ _ _
  | LFassign => label Fassign _ _ _
  | LFseq => label Fseq _ _ _
  | LFif => label Fif _ _ _
  | LKExp => label KExp _ _ _
  | LKBExp => label KBExp _ _ _
  | LKStmt => label KStmt _ _ _
  | LKFreezer => label KFreezer _ _ _
  (* kcfg constructor *)
  | LKCfg => label KCfg _ _ _
  (* klist constructors *)
  | Lkra => label (@cons kitem) _ _ _
  | Lkdot => label (@nil kitem) _ _ _
 end);
try give_type.

Defined.

Module ImpLabels <: Labels.
  Definition Sort := Sort.
  Definition sort_sem := sort_sem.
  Definition sort_dec := sort_dec.

  Fixpoint optype args result :=
    match args with
      | nil => sort_sem result
      | arg :: args => sort_sem arg -> optype args result
    end.

  Definition Label := Label.
  Definition label_sem := label_sem.
End ImpLabels.

Module ImpLang <: ObjectLanguage := GenericLang ImpLabels.

Module TermAbbrevs.

Definition TApp (l : Label) ts := @ImpLang.TApp positive l ts.
Definition TMVar := @ImpLang.TMVar positive.

Definition Id i := TApp (LId i) nil.
Definition Val i := TApp (LVal i) nil.
Definition Bool b := TApp (LBool b) nil.
Definition Store s := TApp (LStore s) nil.

Definition negb b := TApp Lnegb [b].
Definition Nez x :=  TApp LNez [x].
Definition Zleb x y := TApp LZleb [x;y].
Definition Skip := TApp LSkip nil.
Definition Ehole := TApp LEhole nil.
Definition Bhole := TApp LBhole nil.
Definition Shole := TApp LShole nil.

Definition isEVal e := TApp LisEVal [e].
Definition isBool b := TApp LisBool [b].

Definition EVar x := TApp LEVar [x].
Definition ECon x := TApp LECon [x].
Definition BCon x := TApp LBCon [x].
Definition BNot x := TApp LBNot [x].

Definition PlusZ x y := TApp LPlusZ [x;y].
Definition DivZ x y := TApp LDivZ [x;y].
Definition Lookup x y := TApp LLookup [x;y].
Definition EPlus x y := TApp LEPlus [x;y].
Definition EDiv x y := TApp LEDiv [x;y].
Definition BLe x y := TApp LBLe [x;y].
Definition BAnd x y := TApp LBAnd [x;y].

Definition SAssign x y := TApp LSAssign [x;y].
Definition Seq x y := TApp LSeq [x;y].
Definition SWhile x y := TApp LSWhile [x;y].
Definition Cfg x y := TApp LCfg [x;y].
Definition ECfg x y := TApp LECfg [x;y].
Definition BCfg x y := TApp LBCfg [x;y].
Definition SCfg x y := TApp LSCfg [x;y].
Definition plusl x y := TApp Lplusl [x;y].
Definition plusr x y := TApp Lplusr [x;y].
Definition divl x y := TApp Ldivl [x;y].
Definition divr x y := TApp Ldivr [x;y].
Definition lel x y := TApp Llel [x;y].
Definition ler x y := TApp Ller [x;y].
Definition andlE x y := TApp LandlE [x;y].
Definition andlB x y := TApp LandlB [x;y].
Definition assigne x y := TApp Lassigne [x;y].
Definition seqE x y := TApp LseqE [x;y].
Definition seqB x y := TApp LseqB [x;y].
Definition seqS x y := TApp LseqS [x;y].
Definition whilecE x y := TApp LwhilecE [x;y].
Definition whilecB x y := TApp LwhilecB [x;y].
Definition cfgcE x y := TApp LcfgcE [x;y].
Definition cfgcB x y := TApp LcfgcB [x;y].
Definition cfgcS x y := TApp LcfgcS [x;y].
Definition plugE x y := TApp LplugE [x;y].
Definition plugB x y := TApp LplugB [x;y].
Definition plugS x y := TApp LplugS [x;y].

Definition Update x y z := TApp LUpdate [x;y;z].
Definition SIf x y z := TApp LSIf [x;y;z].
Definition ifcE x y z := TApp LifcE [x;y;z].
Definition ifcB x y z := TApp LifcB [x;y;z].

Definition Fplusl x := TApp LFplusl [x].
Definition Fplusr x := TApp LFplusr [x].
Definition Fdivl x := TApp LFdivl [x].
Definition Fdivr x := TApp LFdivr [x].
Definition Flel x := TApp LFlel [x].
Definition Fler x := TApp LFler [x].
Definition Fandl x := TApp LFandl [x].
Definition Fassign x := TApp LFassign [x].
Definition Fseq x := TApp LFseq [x].
Definition Fif x y := TApp LFif [x;y].

Definition KExp x := TApp LKExp [x].
Definition KBExp x := TApp LKBExp [x].
Definition KStmt x := TApp LKStmt [x].
Definition KFreezer x := TApp LKFreezer [x].

Definition KCfg x y := (TApp LKCfg [x;y]).

Definition kra x y := TApp Lkra [x;y].
Definition kdot := TApp Lkdot nil.

Ltac term_quote t cont :=
  match t with
    | domains.hole Exp => cont Ehole
    | domains.hole BExp => cont Bhole
    | domains.hole Stmt => cont Shole
    | domains.isEVal ?e =>
        term_quote e ltac:(fun et =>
          let pt := constr:(isEVal et) in
            cont pt)
    | domains.isBool ?b =>
        term_quote b ltac:(fun bt =>
          let pt := constr:(isBool bt) in
            cont pt)

    | domains.EVar ?v =>
        term_quote v ltac:(fun vt => let et := constr:(EVar vt) 
                                     in cont et)
    | domains.ECon ?x =>
        term_quote x ltac:(fun xt => let et := constr:(ECon xt) 
                                     in cont et)
    | domains.BCon ?v =>
        term_quote v ltac:(fun vt => let et := constr:(BCon vt) 
                                     in cont et)
    | domains.BNot ?x =>
        term_quote x ltac:(fun xt => let et := constr:(BNot xt) 
                                     in cont et)
    | Zplus ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(PlusZ xt yt)
              in cont rt))
    | Zdiv ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(DivZ xt yt)
              in cont rt))
    | domains.lookup ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(Lookup xt yt)
              in cont rt))
    | domains.EPlus ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(EPlus xt yt)
              in cont rt))
    | domains.EDiv ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(EDiv xt yt)
              in cont rt))
    | domains.BLe ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(BLe xt yt)
              in cont rt))
    | domains.BAnd ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(BAnd xt yt)
              in cont rt))
    | domains.SAssign ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(SAssign xt yt)
              in cont rt))
    | domains.Seq ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(Seq xt yt)
              in cont rt))
    | domains.SWhile ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(SWhile xt yt)
              in cont rt))
    | domains.Cfg ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(Cfg xt yt)
              in cont rt))
    | domains.ECfg ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(ECfg xt yt)
              in cont rt))
    | domains.BCfg ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(BCfg xt yt)
              in cont rt))
    | (@domains.plusl Exp) ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(plusl xt yt)
              in cont rt))
    | (@domains.plusr Exp) ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(plusr xt yt)
              in cont rt))
    | (@domains.divl Exp) ?x ?y =>
     term_quote x ltac:(fun xt =>
       term_quote y ltac:(fun yt =>
         let rt := constr:(divl xt yt)
           in cont rt))
    | (@domains.divr Exp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(divr xt yt)
            in cont rt))
    | (@domains.lel Exp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(lel xt yt)
            in cont rt))
    | (@domains.ler Exp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(ler xt yt)
            in cont rt))
    | (@domains.andl Exp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(andlE xt yt)
            in cont rt))
    | (@domains.andl BExp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(andlB xt yt)
            in cont rt))
    | (@domains.assigne Exp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(assigne xt yt)
            in cont rt))
    | (@domains.seqc Exp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(seqE xt yt)
            in cont rt))
    | (@domains.seqc BExp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(seqB xt yt)
            in cont rt))
    | (@domains.seqc Stmt) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(seqS xt yt)
            in cont rt))
    | (@domains.whilec Exp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(whilecE xt yt)
            in cont rt))
    | (@domains.whilec BExp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(whilecB xt yt)
            in cont rt))
    | (@domains.cfgc Exp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(cfgcE xt yt)
            in cont rt))
    | (@domains.cfgc BExp) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(cfgcB xt yt)
            in cont rt))
    | (@domains.cfgc Stmt) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(cfgcS xt yt)
            in cont rt))
    | (@domains.plug Exp cfg) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(plugE xt yt)
            in cont rt))
    | (@domains.plug BExp cfg) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(plugB xt yt)
            in cont rt))
    | (@domains.plug Stmt cfg) ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(plugS xt yt)
            in cont rt))

    | domains.SIf ?x ?y ?z =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          term_quote z ltac:(fun zt =>
            let rt := constr:(SIf xt yt zt)
              in cont rt)))
    | (@domains.ifc Exp) ?x ?y ?z =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          term_quote z ltac:(fun zt =>
            let rt := constr:(ifcE xt yt zt)
              in cont rt)))
    | (@domains.ifc BExp) ?x ?y ?z =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          term_quote z ltac:(fun zt =>
            let rt := constr:(ifcB xt yt zt)
              in cont rt)))
    | domains.update ?x ?y =>
        term_quote x ltac:(fun xt =>
          term_quote y ltac:(fun yt =>
            let rt := constr:(Update xt yt)
              in cont rt))
    | domains.Fplusl ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Fplusl xt)
          in cont rt)
    | domains.Fplusr ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Fplusr xt)
          in cont rt)
    | domains.Fdivl ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Fdivl xt)
          in cont rt)
    | domains.Fdivr ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Fdivr xt)
          in cont rt)
    | domains.Flel ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Flel xt)
          in cont rt)
    | domains.Fler ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Fler xt)
          in cont rt)
    | domains.Fandl ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Fandl xt)
          in cont rt)
    | domains.Fassign ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Fassign xt)
          in cont rt)
    | domains.Fseq ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(Fseq xt)
          in cont rt)
    | domains.KExp ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(KExp xt)
          in cont rt)
    | domains.KBExp ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(KBExp xt)
          in cont rt)
    | domains.KStmt ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(KStmt xt)
          in cont rt)
    | domains.KFreezer ?x =>
      term_quote x ltac:(fun xt =>
        let rt := constr:(KFreezer xt)
          in cont rt)

  | domains.Fif ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(Fif xt yt)
            in cont rt))
  | domains.KCfg ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(KCfg xt yt)
            in cont rt))
  | domains.kra ?x ?y =>
      term_quote x ltac:(fun xt =>
        term_quote y ltac:(fun yt =>
          let rt := constr:(kra xt yt)
            in cont rt))

  | domains.kdot =>
      cont kdot
  | domains.Skip => cont Skip
  | true => let rt := constr:(Bool true)
             in cont rt
  | false => let rt := constr:(Bool false)
             in cont rt
  | _ =>
      let H := fresh in
        evar (H:ImpLang.Base.T);cont H;unfold H in * |- *; clear H
  (* might want to somehow find integer literal eventually *)
  end
    .

Ltac align_rule val term env cont :=
  let pair := constr:(val,term) in
  match pair with
    | (domains.KCfg ?sv ?ev, KCfg ?st ?et) =>
      align_rule sv st env ltac:(fun env' =>
        align_rule ev et env' cont)
    | (domains.KExp ?ev, KExp ?et) =>
      align_rule ev et env cont
    | (domains.KBExp ?ev, KBExp ?et) =>
      align_rule ev et env cont
    | (domains.KStmt ?sv, KStmt ?st) =>
      align_rule sv st env cont
    | (domains.KFreezer ?fv, KFreezer ?ft) =>
      align_rule fv ft env cont
    | (domains.kra ?iv ?rv, kra ?it ?rt) =>
      align_rule iv it env ltac:(fun env' =>
        align_rule rv rt env' cont)
    | (domains.SAssign ?xv ?ev, SAssign ?xt ?et) =>
      align_rule xv xt env ltac:(fun env' =>
        align_rule ev et env' cont)
    | (domains.SIf ?bv ?tv ?ev, SIf ?bt ?tt ?et) =>
      align_rule bv bt env ltac:(fun env' =>
        align_rule tv tt env' ltac:(fun env'' =>
          align_rule ev et env'' cont))
    | (domains.SWhile ?xv ?ev, SWhile ?xt ?et) =>
      align_rule xv xt env ltac:(fun env' =>
        align_rule ev et env' cont)
    | (domains.Seq ?xv ?ev, Seq ?xt ?et) =>
      align_rule xv xt env ltac:(fun env' =>
        align_rule ev et env' cont)
    | (domains.Skip, Skip) => cont env
    | (domains.EPlus ?lv ?rv, EPlus ?lt ?rt) =>
      align_rule lv lt env ltac:(fun env' =>
        align_rule rv rt env' cont)
    | (domains.EDiv ?lv ?rv, EDiv ?lt ?rt) =>
      align_rule lv lt env ltac:(fun env' =>
        align_rule rv rt env' cont)
    | (domains.ECon ?iv, ECon ?it) =>
      align_rule iv it env cont
    | (domains.EVar ?vv, EVar ?vt) =>
      align_rule vv vt env cont
    | (domains.BCon ?iv, BCon ?it) =>
      align_rule iv it env cont
    | (domains.BLe ?lv ?rv, BLe ?lt ?rt) =>
      align_rule lv lt env ltac:(fun env' =>
        align_rule rv rt env' cont)
    | (domains.BAnd ?lv ?rv, BAnd ?lt ?rt) =>
      align_rule lv lt env ltac:(fun env' =>
        align_rule rv rt env' cont)
    | (domains.Fplusl ?v, Fplusl ?t) =>
      align_rule v t env cont
    | (domains.Fplusr ?v, Fplusr ?t) =>
      align_rule v t env cont
    | (domains.Fdivl ?v, Fdivl ?t) =>
      align_rule v t env cont
    | (domains.Fdivr ?v, Fdivr ?t) =>
      align_rule v t env cont
    | (domains.Flel ?v, Flel ?t) =>
      align_rule v t env cont
    | (domains.Fler ?v, Fler ?t) =>
      align_rule v t env cont
    | (domains.Fandl ?v, Fandl ?t) =>
      align_rule v t env cont
    | (domains.Fassign ?v, Fassign ?t) =>
      align_rule v t env cont
    | (domains.Fseq ?v, Fseq ?t) =>
      align_rule v t env cont
    | (domains.Fif ?tv ?ev, Fif ?tt ?et) =>
      align_rule tv tt env ltac:(fun env' =>
        align_rule ev et env' cont)
    | (?b, Bool ?b) => cont env
    | (?v, TMVar ?x) =>
      let t := type of v in
        sort_fold t ltac:(fun s =>
          let env' := constr:(PositiveMap.add x
            (existT sort_sem s v) env)
          in cont env')
  end.

End TermAbbrevs.