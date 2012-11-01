require "matching-logic.k"
require "wcet.k"

module SUM
  imports MATCHING-LOGIC
  imports WCET

  rule <k> add r 1 , r 1 , r 2
           add r 2 , r 2 , #1
           bne Sum:Id , r 2 , r 0 => . ...</k>
       <reg> 0 |-> N:Int 1 |-> (S => N *Int (N +Int 1) /Int 2) 2 |-> (I:Int => N:Int) </reg>
       <progress> true </progress>
       <formula> Phi => Phi andBool S ==Int (I *Int (I +Int 1) /Int 2) </formula> when String2Id("sum") ==K Sum andBool S ==Int (I *Int (I +Int 1) /Int 2)

endmodule
