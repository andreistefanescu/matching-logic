Require Import proofsystem.

Inductive var := Flag0 | Flag1 | Turn.
Record var_map := Store { flag0 : bool; flag1 : bool; turn : bool }.
Definition get v :=
  match v with
    | Flag0 => flag0 
    | Flag1 => flag1
    | Turn => turn
  end.

Definition put v x r :=
  match v with
    | Flag0 => Store x         (flag1 r) (turn r)
    | Flag1 => Store (flag0 r) x         (turn r)
    | Turn  => Store (flag0 r) (flag1 r) x
  end.

Lemma get_put : forall v, (fun x r => get v (put v x r)) = (fun x r => x).
Proof. destruct v; reflexivity. Qed.

Inductive inst :=
  | CriticalSection
  | Assign (v : var) (b : bool)
  | While (v : var) (b : bool) (body : list inst)
  | If (v : var) (b : bool) (body : list inst)
  .

Inductive cfg := Cfg (pgm1 pgm2 : list inst) (store : var_map) | Wrong.

Require Import Bool.

Inductive istep : list inst -> var_map -> list inst -> var_map -> Prop :=
  | cs_dissolve : forall rest env, istep (CriticalSection :: rest) env rest env
  | assign : forall v x rest env, istep (Assign v x :: rest) env rest (put v x env)
  | step_if : forall v x body rest env,
              istep (If v x body :: rest) env
                    ((if eqb (get v env) x then body else nil) ++ rest) env
  | while : forall v x body rest env,
              istep (While v x body :: rest) env
                    ((if eqb (get v env) x then body ++ While v x body :: nil else nil)
                       ++ rest) env
  .
                            
Inductive step : cfg -> cfg -> Prop :=
| left_step : forall pgm1 pgm1' env env', istep pgm1 env pgm1' env' -> forall pgm2,
     step (Cfg pgm1 pgm2 env) (Cfg pgm1' pgm2 env')
| right_step : forall pgm2 pgm2' env env', istep pgm2 env pgm2' env' -> forall pgm1,
     step (Cfg pgm1 pgm2 env) (Cfg pgm1 pgm2' env')
| crash : forall rest1 rest2 env,
            step (Cfg (CriticalSection :: rest1) (CriticalSection :: rest2) env)
                 Wrong.

CoInductive allreach (gamma : cfg) (phi : cfg -> Prop) : Prop :=
  | reach_here : phi gamma -> allreach gamma phi
  | reach_next : (exists gamma', step gamma gamma') ->
                 (forall gamma', step gamma gamma' ->
                                 allreach gamma' phi) ->
                 allreach gamma phi.

Require Import List.

Fixpoint inst_tails (i : inst) (rest : list inst) : list (list inst) :=
  let block_tails := fix block_tails b rest :=
      match b with
        | nil => nil
        | i :: b' => inst_tails i (b' ++ rest) ++ block_tails b' rest
      end in
  (i :: rest) ::
  match i with
    | CriticalSection => nil
    | Assign _ _ => nil
    | If _ _ body => block_tails body rest
    | While _ _ body => block_tails body (i :: rest)
  end.

Fixpoint pgm_tails pgm rest : list (list inst) :=
  match pgm with
    | nil => nil
    | i :: b' => inst_tails i (b' ++ rest) ++ pgm_tails b' rest
  end.

Fixpoint atLine (n : nat) (pgm : list inst) : list inst :=
  nth n (pgm_tails pgm nil) nil.

Definition dekker0 : list inst :=
  Assign Flag0 true ::
  While Flag1 true
   (If Turn true
       (Assign Flag0 false ::
        While Turn true nil ::
        Assign Flag0 true ::
        nil) ::
    nil) ::
  CriticalSection ::
  Assign Turn true ::
  Assign Flag0 false ::
  nil.

Definition dekker1 : list inst :=
  Assign Flag1 true ::
  While Flag0 true
   (If Turn false
       (Assign Flag1 false ::
        While Turn false nil ::
        Assign Flag1 true ::
        nil) ::
    nil) ::
  CriticalSection ::
  Assign Turn false ::
  Assign Flag1 false ::
  nil.

Definition flag0_invariant c :=
  match c with
    | Wrong => False
    | Cfg pgm0 _ store =>
      In pgm0 (map (fun l => atLine l dekker0)
         (if flag0 store then (1::2::3::6::7::8::nil) else (0::4::5::9::nil)))
  end.

Definition flag1_invariant c :=
  match c with
    | Wrong => False
    | Cfg _ pgm1 store =>
      In pgm1 (map (fun l => atLine l dekker1)
         (if flag1 store then (1::2::3::6::7::8::nil) else (0::4::5::9::nil)))
  end.
                 
Definition exclusion c :=
  match c with
    | Wrong => False
    | Cfg pgm0 pgm1 _ =>
      ~ (In pgm0 (map (fun l => atLine l dekker0) (6::7::8::nil)) /\
         In pgm1 (map (fun l => atLine l dekker1) (6::7::8::nil)))
  end.

Lemma one_shot_exclusion : forall c,
  flag0_invariant c -> flag1_invariant c -> exclusion c ->                           
  allreach c (fun cfg => match cfg with
                           | Cfg nil nil _ => True
                           | _ => False
                         end).
cofix.
intros.
assert (forall c', step c c' -> (flag0_invariant c' /\ flag1_invariant c' /\ exclusion c')).
intros.
split;[|split].
(* flag 0 invariant *)
destruct H2.
clear H0 H1.
destruct env.
simpl in * |- *.
destruct flag2.
simpl in H.  intuition; subst.
inversion H2;[subst; destruct flag1; simpl; tauto].
inversion H2;[subst; destruct turn; simpl; tauto].
inversion H2;[subst; simpl; tauto].
inversion H2;[subst; simpl; tauto].
inversion H2;[subst; simpl; tauto].
inversion H2;[subst; simpl; tauto].
simpl in H. intuition; subst.
inversion H2;[subst; simpl; tauto].
inversion H2;[subst; destruct turn; simpl; tauto].
inversion H2;[subst; simpl; tauto].
inversion H2.
(* done stepping in pgm1 *)
(* for steps in pgm2, just need to show they all preserve flag1 *)
simpl. replace (flag0 env') with (flag0 env).
assumption.
destruct env.
clear H H1; simpl in H0.
destruct flag3; simpl in H0; intuition;subst;
inversion H2; simpl;reflexivity.

destruct env.
destruct flag2; simpl in H;  intuition (try discriminate).
injection H; intro; subst; clear H.
destruct flag3; simpl in H0;  intuition (try discriminate).
injection H0; intro; subst; clear H0.
destruct H1.
simpl. intuition.

(* done with flag0 invariant, same story for flag1 invariant *)
destruct H2.
(* for steps in pgm1, just need to show they all preserve flag2 *)
simpl. replace (flag1 env') with (flag1 env).
assumption.
destruct env.
clear H0 H1; simpl in H.
destruct flag2; simpl in H; intuition;subst;
inversion H2; simpl;reflexivity.
(* steps in pgm2 need to be done *)
clear H H1.
destruct env.
simpl in * |- *.
destruct flag3.
simpl in H0.  intuition; subst.
inversion H2;[subst; destruct flag2; simpl; tauto].
inversion H2;[subst; destruct turn; simpl; tauto].
inversion H2;[subst; simpl; tauto].
inversion H2;[subst; simpl; tauto].
inversion H2;[subst; simpl; tauto].
inversion H2;[subst; simpl; tauto].
simpl in H0. intuition; subst.
inversion H2;[subst; simpl; tauto].
inversion H2;[subst; destruct turn; simpl; tauto].
inversion H2;[subst; simpl; tauto].
inversion H2.
(* need to show we can't be Wrong *)
destruct env.
destruct flag2; simpl in H;  intuition (try discriminate).
injection H; intro; subst; clear H.
destruct flag3; simpl in H0;  intuition (try discriminate).
injection H0; intro; subst; clear H0.
destruct H1.
simpl. intuition.

Focus 2.
destruct c;[|destruct H].
destruct pgm1.
destruct pgm2.
apply reach_here. exact I.
apply reach_next.
destruct i;eexists;apply right_step; constructor.
intros. specialize (H2 _ H3). destruct H2. destruct H4. auto.

apply reach_next.
destruct i;eexists;apply left_step; constructor.
intros. specialize (H2 _ H3). destruct H2. destruct H4. auto.

(* condition holds up to here *)
(* exclusion steps? *)
destruct H2.

Focus 3.
destruct env.
destruct flag2; simpl in H;  intuition (try discriminate).
injection H; intro; subst; clear H.
destruct flag3; simpl in H0;  intuition (try discriminate).
injection H0; intro; subst; clear H0.
destruct H1.
simpl. intuition.

(* left step *)
unfold exclusion in H1 |- *.
intro.
destruct H3.
assert (~(In pgm1 (map (fun l : nat => atLine l dekker0) (6 :: 7 :: 8 :: nil)))).
intro; apply H1; split; assumption.
clear H1.

destruct env.
simpl in H, H0.
destruct flag3;[clear H0 H4 |
clear -H0 H4;solve[simpl in H0, H4; intuition (subst; discriminate)]].

destruct flag2;
cbv zeta iota beta delta -[atLine dekker0 dekker1] in H, H3, H5.
decompose sum H; clear H; try solve[apply H5; auto]; clear H5.
subst; simpl in H2; inversion H2; subst; clear -H3; simpl in H3; decompose sum H3; discriminate.
destruct turn0;subst; simpl in H2; inversion H2; subst; clear -H3; simpl in H3; decompose sum H3; try discriminate.
subst; simpl in H2; inversion H2; subst; clear -H3; simpl in H3; decompose sum H3; discriminate.
decompose sum H; clear H; try solve[apply H5; auto]; clear H5.
subst; simpl in H2; inversion H2; subst; clear -H3; simpl in H3; decompose sum H3; discriminate.
destruct turn0; subst; simpl in H2; inversion H2; subst; clear -H3; simpl in H3; decompose sum H3; discriminate.
subst; simpl in H2; inversion H2; subst; clear -H3; simpl in H3; decompose sum H3; discriminate.
subst; simpl in H2; inversion H2; subst; clear -H3; simpl in H3; decompose sum H3; discriminate.

(* right side step? *)
unfold exclusion in H1 |- *.
intro.
destruct H3.
assert (~(In pgm2 (map (fun l : nat => atLine l dekker1) (6 :: 7 :: 8 :: nil)))).
intro; apply H1; split; assumption. 
clear H1.

destruct env.
simpl in H, H0.
destruct flag2;[clear H H3|clear -H H3;
solve[simpl in H, H3; intuition (subst; discriminate)]].

destruct flag3;
cbv zeta iota beta delta -[atLine dekker0 dekker1] in H0, H4, H5.
decompose sum H0; clear H0; try solve[apply H5; auto]; clear H5.
subst; simpl in H2; inversion H2; subst; clear -H4; simpl in H4; decompose sum H4; discriminate.
destruct turn0;subst; simpl in H2; inversion H2; subst; clear -H4; simpl in H4; decompose sum H4; discriminate.
subst; simpl in H2; inversion H2; subst; clear -H4; simpl in H4; decompose sum H4; discriminate.
decompose sum H0; clear H0; try solve[apply H5; auto]; clear H5.
subst; simpl in H2; inversion H2; subst; clear -H4; simpl in H4; decompose sum H4; discriminate.
destruct turn0;subst; simpl in H2; inversion H2; subst; clear -H4; simpl in H4; decompose sum H4; discriminate.
subst; simpl in H2; inversion H2; subst; clear -H4; simpl in H4; decompose sum H4; discriminate.
subst; simpl in H2; inversion H2; subst; clear -H4; simpl in H4; decompose sum H4; discriminate.
Qed.