Require Import proofsystem.

(* A very simple example of the proof system, showing that
   the system over pairs of natural numbers where the
   steps decrement one side or the other reach zero *)

Definition cfg := prod nat nat.
Inductive step : cfg -> cfg -> Prop :=
  | stepl : forall n m, step (S n, m) (n, m)
  | stepr : forall n m, step (n, S m) (n, m)
.

CoInductive allreach (gamma : cfg) (phi : cfg -> Prop) : Prop :=
  | reach_here : phi gamma -> allreach gamma phi
  | reach_next : (exists gamma', step gamma gamma') ->
                 (forall gamma', step gamma gamma' ->
                                 allreach gamma' phi) ->
                 allreach gamma phi.

Require Import Arith.
Definition cfg_dec : forall (c c' : cfg), {c=c'}+{c<>c'}.
destruct c.
destruct c'.  
destruct (eq_nat_dec n n1);[|right;congruence].
destruct (eq_nat_dec n0 n2);[|right;congruence].
left. congruence.
Qed.

Lemma steps_nonzeros : forall cfg, (0,0) <> cfg -> exists cfg', step cfg cfg'.
destruct cfg0.
destruct n;[destruct n0;[congruence|]|];(eexists;constructor).
Qed.

Lemma semantic_reach_zero : forall cfg, allreach cfg (eq (0,0)).
cofix.
intro. destruct (cfg_dec (0,0) cfg0);
constructor (solve[auto using steps_nonzeros]).
Qed.

Definition empty_system : forall {cfg}, system cfg :=
  fun _ _ _ _ => False.

Definition is_conseq_l : forall ax (strict : bool) (env : Type)
                (phi1 phi1' phi2 : formula cfg env),
                (forall (g : cfg) (e : env), phi1 g e -> phi1' g e) ->
                IS cfg step ax strict env phi1' phi2 ->
                IS cfg step ax strict env phi1 phi2.
intros. eapply is_conseq; eauto.
Defined.

Lemma split_case : forall ax (strict : bool) (env : Type)
                (phi1 check phi2 : formula cfg env),

                  (forall g e, check g e \/ ~check g e) ->
                IS cfg step ax strict env (fun env cfg => check env cfg /\ phi1 env cfg) phi2 ->
                IS cfg step ax strict env (fun env cfg => (~ check env cfg) /\ phi1 env cfg) phi2 ->
                IS cfg step ax strict env phi1 phi2.
intros.
apply is_conseq_l with
  (phi1' := fun env cfg =>
            (check env cfg /\ phi1 env cfg) \/ (~check env cfg /\ phi1 env cfg))
;[clear -H;firstorder |apply is_case;assumption].
Qed.
Lemma proof_reach_zero : IS _ step empty_system false cfg
   (fun env cfg => cfg = env) (fun env cfg => cfg = (0,0)).
Proof.
apply split_case with (check := (fun env _ => env = (0,0))).
intros. destruct (cfg_dec g (0,0)); solve[auto].

eapply is_conseq_l;[|apply is_refl].
intros; intuition congruence.

(* nonzero case *)

(* incomplete *)
Admitted.
