require "../../lib/matching-logic.k"
require "../../wcet.k"
require "../../wcet-domain-reasoning.k"

module SUM
  imports MATCHING-LOGIC
  imports WCET
  imports WCET-DOMAIN-REASONING

  syntax #Id ::= "main" | "sum"

  rule [invariant] : <k> add r 2 , r 2 , #1
           add r 1 , r 1 , r 2
	   bne sum , r 2 , r 0
           halt => halt </k>
       <pgm> main |-> or r 0 , #10 , #0 //TODO: remove
                      or r 1 , #0 , #0
                      or r 2 , #0 , #0
/*                    li r 0 , #10
                      li r 1 , #0
                      li r 2 , #0 */
                      jmp sum
             sum |-> add r 2 , r 2 , #1
                     add r 1 , r 1 , r 2
                     bne sum , r 2 , r 0
                     halt </pgm>
       <reg> 0 |-> N:Int 1 |-> (S:Int => N *Int (N +Int 1) /Int 2) 2 |-> (I:Int => N:Int) </reg>
       <formula> Phi:Bool </formula>
       <progress> true </progress> when checkSat(notBool(Phi impliesBool (S ==Int (I *Int (I +Int 1) /Int 2)))) ==String "unsat" [structural]

  rule [invariant-fails] : <task>... <k> add r 2 , r 2 , #1
           add r 1 , r 1 , r 2
	   bne sum , r 2 , r 0
           halt </k>
       <pgm> main |-> or r 0 , #10 , #0 //TODO: remove
                      or r 1 , #0 , #0
                      or r 2 , #0 , #0
/*                    li r 0 , #10
                      li r 1 , #0
                      li r 2 , #0 */
                      jmp sum
             sum |-> add r 2 , r 2 , #1
                     add r 1 , r 1 , r 2
                     bne sum , r 2 , r 0
                     halt </pgm>
       <reg> 0 |-> N:Int 1 |-> (S:Int) 2 |-> (I:Int) </reg>
       <formula> Phi:Bool </formula>
       <progress> true </progress> ...</task> => stuck when checkSat(notBool(Phi impliesBool (S ==Int (I *Int (I +Int 1) /Int 2)))) =/=String "unsat" [structural]


 /*
  pre <reg> 0 |-> N:Int 1 |-> (S:Int => N *Int (N +Int 1) /Int 2) 2 |-> (I:Int => N:Int) </reg> when S ==Int (I *Int (I +Int 1) /Int 2)
  post true

=>

  <k>
    add r 2 , r 2 , #1
    add r 1 , r 1 , r 2
    bne sum , r 2 , r 0
    halt => halt
  </k>
  <pgm>
    main |-> li r 0 , #10
             li r 1 , #0
             li r 2 , #0
             jmp sum
    sum |-> add r 2 , r 2 , #1
            add r 1 , r 1 , r 2
            bne sum , r 2 , r 0
            halt
  </pgm>
  <reg> 0 |-> N:Int 1 |-> (S:Int => N *Int (N +Int 1) /Int 2) 2 |-> (I:Int => N) </reg> when S ==Int (I *Int (I +Int 1) /Int 2)
*/

endmodule
