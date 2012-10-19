Require Import ZArith.

Require Import domains.

Inductive step : sosCfg -> sosCfg -> Prop :=
  | lookup : forall v env,
      step (ECfg (EVar v) env) (ECfg (ECon (lookup env v)) env)
  | plusl : forall l l' r env,
      step (ECfg l env) (ECfg l' env) ->
      step (ECfg (EPlus l r) env) (ECfg (EPlus l' r) env)
  | plusr : forall l r r' env,
      step (ECfg r env) (ECfg r' env) ->
      step (ECfg (EPlus l r) env) (ECfg (EPlus l r') env)
  | plusc : forall x y env,
      step (ECfg (EPlus (ECon x) (ECon y)) env)
           (ECfg (ECon (x+y)%Z) env)
  | divl : forall l l' r env,
      step (ECfg l env) (ECfg l' env) ->
      step (ECfg (EDiv l r) env) (ECfg (EDiv l' r) env)
  | divr : forall l r r' env,
      step (ECfg r env) (ECfg r' env) ->
      step (ECfg (EPlus l r) env)
           (ECfg (EPlus l r') env)
  | divc : forall x y env, y <> 0%Z ->
      step (ECfg (EDiv (ECon x) (ECon y)) env)
           (ECfg (ECon (x / y)%Z) env)
  | lel : forall l l' r env,
      step (ECfg l env) (ECfg l' env) ->
      step (BCfg (BLe l r) env) (BCfg (BLe l' r) env)
  | ler : forall x r r' env,
      step (ECfg r env) (ECfg r' env) ->
      step (BCfg (BLe (ECon x) r) env) (BCfg (BLe (ECon x) r) env)
  | lec : forall x y env,
      step (BCfg (BLe (ECon x) (ECon y)) env)
           (BCfg (BCon (Zle_bool x y)) env)
  | nots : forall b b' env,
      step (BCfg b env) (BCfg b' env) ->
      step (BCfg (BNot b) env) (BCfg (BNot b') env)
  | notc : forall b env,
      step (BCfg (BNot (BCon b)) env)
           (BCfg (BCon (negb b)) env)
  | andl : forall l l' r env,
      step (BCfg l env) (BCfg l' env) ->
      step (BCfg (BAnd l r) env) (BCfg (BAnd l' r) env)
  | andc : forall b r env,
      step (BCfg (BAnd (BCon b) r) env)
           (BCfg (if b then r else BCon false) env)
 (*
  | andt : forall r env,
      step (BCfg (BAnd (BCon true) r) env)
           (BCfg r env)
  | andf : forall r env,
      step (BCfg (BAnd (BCon false) r) env)
           (BCfg (BCon false) env)
  *)
  | assinge : forall v e e' env,
      step (ECfg e env) (ECfg e' env) ->
      step (SCfg (SAssign v e) env) (SCfg (SAssign v e') env)
  | assignc : forall v x env,
      step (SCfg (SAssign v (ECon x)) env)
           (SCfg Skip (update env v x))
  | seql : forall s env s' env' s2,
      step (SCfg s env) (SCfg s' env') ->
      step (SCfg (Seq s s2) env) (SCfg (Seq s' s2) env')
  | seqr : forall s env, (* make structural ? *)
      step (SCfg (Seq Skip s) env) (SCfg s env)
  | ife : forall c c' s1 s2 env,
      step (BCfg c env) (BCfg c' env) ->
      step (SCfg (SIf c s1 s2) env)
           (SCfg (SIf c' s1 s2) env)
  | ifc : forall b s1 s2 env,
      step (SCfg (SIf (BCon b) s1 s2) env)
           (SCfg (if b then s1 else s2) env)
 (*
  | if_t : forall b s1 s2 env,
      step (SCfg (SIf (BCon true) s1 s2) env)
           (SCfg s1 env)
  | if_f : forall b s1 s2 env,
      step (SCfg (SIf (BCon false) s1 s2) env)
           (SCfg s) env)
  *)
  | whileu : forall c b env, (* structural at head? *)
      step (SCfg (SWhile c b) env)
           (SCfg (SIf c (Seq b (SWhile c b)) Skip) env)
  .
