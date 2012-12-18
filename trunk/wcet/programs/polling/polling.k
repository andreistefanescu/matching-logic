require "../../lib/matching-logic.k"
require "../../wcet.k"
require "../../wcet-domain-reasoning.k"

module POLLING
  imports MATCHING-LOGIC
  imports WCET
  imports WCET-DOMAIN-REASONING

  syntax #Id ::= "main" | "loop" | "data"

  rule [invariant] : 
    <k> rw r 1 , data , #0
        load r 2 , #0
        add r 2 , r 2 , r 1
        store #0, r 2
        sub r 0 , r 0 , #1
        bne loop , r 0 , #0
        halt => .K </k>
    <pgm> main |-> store #0, #0
                   or r 0 , # _ , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   jmp loop
          loop |-> rw r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
    <reg> 0 |-> (N:Int => 0) 1 |-> (_ => FreshR1:Int) 2 |-> (_ => FreshR2:Int) </reg>
    <mem> 0 |-> (Sum:Int => Sum +Int Data +Int Data1 +Int Data2) </mem>
    <status> data |-> (Data:Int => 0) </status>
    <input> ListItem((Time1:Int, data |-> Data1:Int)) ListItem((Time2:Int, data |-> Data2:Int)) => . </input>
    <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6</timing>
    <wcet> Time:Int => Time +Int N *Int 16 +Int 1 </wcet>
    <formula> Phi:Bool </formula>
    <progress> true </progress> when isValid(Phi impliesBool (Time2 -Int Time1 >Int 16 andBool Time <Int Time1 andBool Time +Int (N -Int 1) *Int 16 >Int Time2 andBool (Time2 -Int Time) >Int 3 andBool (Time1 -Int Time) >Int 3)) andBool fresh(FreshR1) andBool fresh(FreshR2) [structural]

  rule [invariant-fails] : <task>...
    <k> rw r 1 , data , #0
        load r 2 , #0
        add r 2 , r 2 , r 1
        store #0, r 2
        sub r 0 , r 0 , #1
        bne loop , r 0 , #0
        halt </k>
    <pgm> main |-> store #0, #0
                   or r 0 , # _ , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   jmp loop
          loop |-> rw r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
    <reg> 0 |-> (N:Int) 1 |-> (_) 2 |-> (_) </reg>
    <mem> 0 |-> (Sum:Int) </mem>
    <status> data |-> Data:Int </status>
    <input> ListItem((Time1:Int, data |-> Data1:Int)) ListItem((Time2:Int, data |-> Data2:Int)) </input>
    <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6</timing>
    <wcet> Time:Int </wcet>
    <formula> Phi:Bool </formula>
    <progress> true </progress> ...</task> => stuck((Phi impliesBool (Time2 -Int Time1 >Int 16 andBool Time <Int Time1 andBool Time +Int (N -Int 1) *Int 16 >Int Time2 andBool (Time2 -Int Time) >Int 3 andBool (Time1 -Int Time) >Int 3))) when notBool isValid(Phi impliesBool (Time2 -Int Time1 >Int 16 andBool Time <Int Time1 andBool Time +Int (N -Int 1) *Int 16 >Int Time2 andBool (Time2 -Int Time) >Int 3 andBool (Time1 -Int Time) >Int 3)) [structural]

  rule [invariant] : 
    <k> rw r 1 , data , #0
        load r 2 , #0
        add r 2 , r 2 , r 1
        store #0, r 2
        sub r 0 , r 0 , #1
        bne loop , r 0 , #0
        halt => .K </k>
    <pgm> main |-> store #0, #0
                   or r 0 , # _ , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   jmp loop
          loop |-> rw r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
    <reg> 0 |-> (N:Int => 0) 1 |-> (_ => FreshR1:Int) 2 |-> (_ => FreshR2:Int) </reg>
    <mem> 0 |-> (Sum:Int => Sum +Int Data +Int Data2) </mem>
    <status> data |-> (Data:Int => 0) </status>
    <input> ListItem((Time2:Int, data |-> Data2:Int)) => . </input>
    <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6</timing>
    <wcet> Time:Int => Time +Int N *Int 16 +Int 1 </wcet>
    <formula> Phi:Bool </formula>
    <progress> true </progress> when isValid(Phi impliesBool (Time <Int Time2 andBool Time +Int (N -Int 1) *Int 16 >Int Time2 andBool (Time2 -Int Time) >Int 3)) andBool fresh(FreshR1) andBool fresh(FreshR2) [structural]

  rule [invariant-fails] : <task>...
    <k> rw r 1 , data , #0
        load r 2 , #0
        add r 2 , r 2 , r 1
        store #0, r 2
        sub r 0 , r 0 , #1
        bne loop , r 0 , #0
        halt </k>
    <pgm> main |-> store #0, #0
                   or r 0 , # _ , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   jmp loop
          loop |-> rw r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
    <reg> 0 |-> (N:Int) 1 |-> (_) 2 |-> (_) </reg>
    <mem> 0 |-> (Sum:Int) </mem>
    <status> data |-> Data:Int </status>
    <input> ListItem((Time2:Int, data |-> Data2:Int)) </input>
    <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6</timing>
    <wcet> Time:Int </wcet>
    <formula> Phi:Bool </formula>
    <progress> true </progress> ...</task> => stuck((Phi impliesBool (Time <Int Time2 andBool Time +Int (N -Int 1) *Int 16 >Int Time2 andBool (Time2 -Int Time) >Int 3))) when notBool isValid(Phi impliesBool (Time <Int Time2 andBool Time +Int (N -Int 1) *Int 16 >Int Time2 andBool (Time2 -Int Time) >Int 3)) [structural]

  rule [invariant] : 
    <k> rw r 1 , data , #0
        load r 2 , #0
        add r 2 , r 2 , r 1
        store #0, r 2
        sub r 0 , r 0 , #1
        bne loop , r 0 , #0
        halt => .K </k>
    <pgm> main |-> store #0, #0
                   or r 0 , # _ , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   jmp loop
          loop |-> rw r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
    <reg> 0 |-> (N:Int => 0) 1 |-> (_ => FreshR1:Int) 2 |-> (_ => FreshR2:Int) </reg>
    <mem> 0 |-> (Sum:Int => Sum +Int Data) </mem>
    <status> data |-> (Data:Int => 0) </status>
    <input> .List</input>
    <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6</timing>
    <wcet> Time:Int => Time +Int N *Int 16 +Int 1 </wcet>
    <formula> Phi:Bool </formula>
    <progress> true </progress> when fresh(FreshR1) andBool fresh(FreshR2) [structural]
/*
  rule [invariant-fails] : <task>...
    <k> rw r 1 , data , #0
        load r 2 , #0
        add r 2 , r 2 , r 1
        store #0, r 2
        sub r 0 , r 0 , #1
        bne loop , r 0 , #0
        halt </k>
    <pgm> main |-> store #0, #0
                   or r 0 , # _ , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   jmp loop
          loop |-> rw r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
    <reg> 0 |-> (N:Int) 1 |-> (_) 2 |-> (_) </reg>
    <mem> 0 |-> (Sum:Int) </mem>
    <status> data |-> Data:Int </status>
    <input> .List </input>
    <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6</timing>
    <wcet> Time:Int </wcet>
    <formula> Phi:Bool </formula>
    <progress> true </progress> ...</task> => stuck((Phi impliesBool (Time >=Int 0))) when notBool isValid(Phi impliesBool (Time >=Int 0)) [structural]

*/

endmodule
