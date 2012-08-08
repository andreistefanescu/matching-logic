Section FO.

Parameter term : Set.

Parameter is_var : term -> Prop.

Parameter term_dec : forall x y : term, {x = y} + {x <> y}.

Definition var : Set := {x : term & (is_var x)}.

Inductive form1 :=
  | Equals1 : term -> term -> form1
  | Forall1 : var -> form1 -> form1
  | And1 : form1 -> form1 -> form1
  | Not1 : form1 -> form1.

Inductive form2 :=
  | Equals2 : term -> term -> form2
(*  | Forall2 : (form2 -> form2) -> form2 *)
  | And2 : form2 -> form2 -> form2
  | Not2 : form2 -> form2.

(*
Inductive form3 :=
  | Equals3 : term -> term -> form3
  | Forall3 : (form3g -> form3) -> form3
  | And3 : form3 -> form3 -> form3
  | Not3 : form3 -> form3
with
  form3g :=
  | guard : form3 -> form3g. *)

Inductive form4 :=
  | Equals4 : term -> term -> form4
  | Forall4 : (var -> form4) -> form4
  | And4 : form4 -> form4 -> form4
  | Not4 : form4 -> form4.

Hypothesis Apply5 : (nat -> term) -> term -> term.

Inductive form5 :=
  | Equals5 : (nat -> term) -> (nat -> term) -> form5
  | Forall5 : nat -> form5 -> form5
  | And5 : form5 -> form5 -> form5
  | Not5 : form5 -> form5.

End.
