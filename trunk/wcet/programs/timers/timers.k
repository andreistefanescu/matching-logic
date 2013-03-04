require "../../lib/matching-logic.k"
require "../../wcet.k"
require "../../wcet-domain-reasoning.k"

module TIMERS
  imports MATCHING-LOGIC
  imports WCET
  imports WCET-DOMAIN-REASONING

  syntax #Id ::= "loop" | "t1" | "t2"

  rule [invariant] :
        <k> sub r 0 , r 0 , #1
            bne loop , r 0 , #0
            halt => .K </k>
   <pgm>
          main |-> or r 0 , #100 , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   int t1 , #7 , #10
                   int t2 , #10 , #15
                   jmp loop
          loop |-> sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt
          t1 |-> add r 1 , r 1 , #1
                 rfi
          t2 |-> add r 2 , r 2 , #1
                 rfi
        </pgm>
      <reg> 0 |-> (N:Int => 0) 1 |-> (T1:Int => T1 +Int #if (Time1 -Int Time) <=Int 3 #then (FinalTime -Int Time) cdivInt 10 #else (FinalTime -Int Time) divInt 10 #fi) 2 |-> (T2:Int => T2 +Int #if (Time2 -Int Time) <=Int 3 #then (FinalTime -Int Time) cdivInt 15 #else (FinalTime -Int Time) divInt 15 #fi) </reg>
          <mem> .Map </mem>
          <status> .Map </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 int |-> 2 rfi |-> 2 </timing>
      <wcet> Time => FinalTime </wcet>
      <timers> ListItem((t1 , (Time1 => FinalTime1), 10))
               ListItem((t2 , (Time2 => FinalTime2), 15))
      </timers>
          <priority> 0 </priority>
          <stack> .List </stack>
          <interrupts> .Set </interrupts>
      <formula> Phi:Bool => Phi andBool FinalTime ==Int Time +Int 3 *Int #if Time1 -Int Time <=Int 3 #then (FinalTime -Int Time) cdivInt 10 #else (FinalTime -Int Time) divInt 10 #fi +Int 3 *Int #if Time2 -Int Time <=Int 3 #then (FinalTime -Int Time) cdivInt 15 #else (FinalTime -Int Time) divInt 15 #fi +Int (3 *Int N) +Int 1 andBool FinalTime1 >Int FinalTime andBool FinalTime2 >Int FinalTime </formula>
      <progress> true </progress> when isValid(Phi impliesBool (N >Int 0 andBool Time1 >Int Time andBool Time2 >Int Time)) andBool fresh(FinalTime:Int) andBool fresh(FinalTime1:Int) andBool fresh(FinalTime2:Int) [structural]

 rule [invariant-fails] : <task>...
        <k> sub r 0 , r 0 , #1
            bne loop , r 0 , #0
            halt </k>
   <pgm>
          main |-> or r 0 , #100 , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   int t1 , #7 , #10
                   int t2 , #10 , #15
                   jmp loop
          loop |-> sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt
          t1 |-> add r 1 , r 1 , #1
                 rfi
          t2 |-> add r 2 , r 2 , #1
                 rfi
        </pgm>
      <reg> 0 |-> (N:Int) 1 |-> (T1:Int) 2 |-> (T2:Int) </reg>
          <mem> .Map </mem>
          <status> .Map </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 int |-> 2 rfi |-> 2 </timing>
      <wcet> Time </wcet>
      <timers> ListItem((t1 , (Time1), 10))
               ListItem((t2 , (Time2), 15))
      </timers>
          <priority> 0 </priority>
          <stack> .List </stack>
          <interrupts> .Set </interrupts>
      <formula> Phi:Bool </formula>
      <progress> true </progress> ...</task> => stuck(Phi impliesBool (N >Int 0 andBool Time1 >Int Time andBool Time2 >Int Time)) when notBool isValid(Phi impliesBool (N >Int 0 andBool Time1 >Int Time andBool Time2 >Int Time)) [structural]

endmodule
