require "../../lib/matching-logic.k"
require "../../wcet.k"
require "../../wcet-domain-reasoning.k"

module POLLING
  imports MATCHING-LOGIC
  imports WCET
  imports WCET-DOMAIN-REASONING

  syntax #Id ::= "main" | "loop" | "data"

  rule [invariant] : 
    <k> read r 1 , data , #0
        load r 2 , #0
        add r 2 , r 2 , r 1
        store #0, r 2
        sub r 0 , r 0 , #1
        bne loop , r 0 , #0
        halt => halt </k>
    <pgm> main |-> store #0, #0
                   or r 0 , #100 , #0
                   jmp loop
          loop |-> read r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
    <reg> 0 |-> (N:Int => 0) 1 |-> (_ => Data2) 2 |-> (_ => Sum +Int Data +Int Data1 +Int Data2) </reg>
    <mem> 0 |-> (Sum:Int => Sum +Int Data +Int Data1 +Int Data2) </mem>
    <status> data |-> (Data:Int => 0) </status>
    <input> Time1:Int |-> Map2KLabel data |-> Data1:Int(.List{K}) Time2:Int |-> Map2KLabel data |-> Data2:Int(.List{K}) </input>
    <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 </timing>
    <wcet> Time:Int => #symInt(4) </wcet>
    <formula> Phi:Bool </formula>
    <progress> true </progress> when checkSat(notBool(Phi impliesBool (Time1 -Int Time >Int 34 andBool Time2 -Int Time1 >Int 34))) ==String "unsat" [structural]

  rule [invariant-fails] : <task>...
    <k> read r 1 , data , #0
        load r 2 , #0
        add r 2 , r 2 , r 1
        store #0, r 2
        sub r 0 , r 0 , #1
        bne loop , r 0 , #0
        halt </k>
    <pgm> main |-> store #0, #0
                   or r 0 , #100 , #0
                   jmp loop
          loop |-> read r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
    <reg> 0 |-> (N:Int) 1 |-> (_) 2 |-> (_) </reg>
    <mem> 0 |-> (Sum:Int) </mem>
    <status> data |-> Data:Int </status>
    <input> Time1:Int |-> Map2KLabel data |-> Data1:Int(.List{K}) Time2:Int |-> Map2KLabel data |-> Data2:Int(.List{K}) </input>
    <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 </timing>
    <wcet> Time:Int </wcet>
    <formula> Phi:Bool </formula>
    <progress> true </progress> ...</task> => stuck when checkSat(notBool(Phi impliesBool (Time1 -Int Time >Int 34 andBool Time2 -Int Time1 >Int 34))) =/=String "unsat" [structural]

endmodule
