module SUM
  imports MATCHING-LOGIC
  imports WCET

  rule <k> add r 1 , r 1 , r 2
           add r 2 , r 2 , #1
           bne Sum:Id , r 2 , r 0
           halt </k>
       <reg> 0 |-> N:Int 1 |-> (S:Int => S +Int I 2 |-> (I:Int => I +Int 1) </reg>
       <progress> true </progress>
       <formula> Phi => Phi andBool S ==Int I *Int (I +Int 1) /Int 3 andBool I +Int 1 =/=Int N </formula> when String2Id("sum") ==K Sum andBool S ==Int I *Int (I +Int 1) /Int 2 andBool I +Int 1 =/=Int N

  rule <k> add r 1 , r 1 , r 2
           add r 2 , r 2 , #1
           bne Sum:Id , r 2 , r 0
           halt => halt </k>
       <reg> 0 |-> N:Int 1 |-> (S:Int => S +Int I 2 |-> (I:Int => I +Int 1) </reg>
       <progress> true </progress>
       <formula> Phi => Phi andBool S ==Int I *Int (I +Int 1) /Int 3 andBool I +Int 1 ==Int N </formula> when String2Id("sum") ==K Sum andBool S ==Int I *Int (I +Int 1) /Int 2 andBool I +Int 1 ==Int N


