Require Import ZArith.

Require Import domains.

Generalizable Variables e s x y b i env.

Inductive eval : sosCfg -> sosCfg -> Prop :=
  | e_var :
    `(eval (ECfg (EVar x) env) (ECfg (ECon (lookup env x)) env))
  | e_plus :
    `(eval (ECfg e1 env) (ECfg (ECon x) env) ->
      eval (ECfg e2 env) (ECfg (ECon y) env) ->
      eval (ECfg (EPlus e1 e2) env) (ECfg (ECon (x + y)%Z) env))
  | e_div :
    `(eval (ECfg e1 env) (ECfg (ECon x) env) ->
      eval (ECfg e2 env) (ECfg (ECon y) env) ->
      y <> 0%Z ->
      eval (ECfg (EDiv e1 e2) env) (ECfg (ECon (x / y)%Z) env))
  | e_le :
    `(eval (ECfg e1 env) (ECfg (ECon x) env) ->
      eval (ECfg e2 env) (ECfg (ECon y) env) ->
      eval (BCfg (BLe e1 e2) env) (BCfg (BCon (Zle_bool x y)) env))
  | e_not :
    `(eval (BCfg e1 env) (BCfg (BCon b) env) ->
      eval (BCfg (BNot e1) env) (BCfg (BCon (negb b)) env))
  | e_and_t :
    `(eval (BCfg e1 env) (BCfg (BCon true) env) ->
      eval (BCfg e2 env) (BCfg (BCon b) env) ->
      eval (BCfg (BAnd e1 e2) env) (BCfg (BCon b) env))
  | e_and_f :
    `(eval (BCfg e1 env) (BCfg (BCon false) env) ->
      eval (BCfg (BAnd e1 e2) env) (BCfg (BCon false) env))
  | e_assign :
    `(eval (ECfg e env) (ECfg (ECon i) env) ->
      eval (SCfg (SAssign x e) env) (SCfg Skip (update env x i)))
  | e_seq :
    `(eval (SCfg s1 env) (SCfg Skip env') ->
      eval (SCfg s2 env') (SCfg Skip env'') ->
      eval (SCfg (Seq s1 s2) env) (SCfg Skip env''))
  | e_if_t :
    `(eval (BCfg e env) (BCfg (BCon true) env) ->
      eval (SCfg s1 env) (SCfg Skip env') ->
      eval (SCfg (SIf e s1 s2) env) (SCfg Skip env'))
  | e_if_f :
    `(eval (BCfg e env) (BCfg (BCon false) env) ->
      eval (SCfg s2 env) (SCfg Skip env') ->
      eval (SCfg (SIf e s1 s2) env) (SCfg Skip env'))
  | e_while :
    `(eval (SCfg (SIf e (Seq s (SWhile e s)) Skip) env)
           (SCfg Skip env') ->
      eval (SCfg (SWhile e s) env) (SCfg Skip env'))
  .