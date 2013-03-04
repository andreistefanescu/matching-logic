<task>
  <lhs>
    <config>
      <T>
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
        <reg> 0 |-> #symInt("N") 1 |-> #symInt("T1") 2 |-> #symInt("T2") </reg>
        <mem> .Map </mem>
        <status> .Map </status>
        <input> .List </input>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 int |-> 2 rfi |-> 2 </timing>
        <wcet> #symInt("Time") </wcet>
        <timers> ListItem((t1 , #symInt("Time1") , 10))
                 ListItem((t2 , #symInt("Time2") , 15))
        </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
      </T>
    </config>
    <formula> #symInt("N") >Int 0 andBool #symInt("Time1") >Int #symInt("Time") andBool #symInt("Time2") >Int #symInt("Time") </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> .K </k>
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
          <reg> 0 |-> 0 1 |-> (#symInt("T1") +Int #if (#symInt("Time1") -Int #symInt("Time")) <=Int 3 #then (#symInt("FinalTime") -Int #symInt("Time")) cdivInt 10 #else (#symInt("FinalTime") -Int #symInt("Time")) divInt 10 #fi) 2 |-> (#symInt("T2") +Int #if (#symInt("Time2") -Int #symInt("Time")) <=Int 3 #then (#symInt("FinalTime") -Int #symInt("Time")) cdivInt 15 #else (#symInt("FinalTime") -Int #symInt("Time")) divInt 15 #fi)
</reg>
          <mem> .Map </mem>
          <status> .Map </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 int |-> 2 rfi |-> 2 </timing>
          <wcet> #symInt("FinalTime") </wcet>
          <timers> ListItem((t1 , #symInt("FinalTime1") , 10))
                   ListItem((t2 , #symInt("FinalTime2") , 15))
          </timers>
          <priority> 0 </priority>
          <stack> .List </stack>
          <interrupts> .Set </interrupts>
        </T>
      </rconfig>
      <rformula> #symInt("FinalTime") ==Int #symInt("Time") +Int 3 *Int #if #symInt("Time1") -Int #symInt("Time") <=Int 3 #then (#symInt("FinalTime") -Int #symInt("Time")) cdivInt 10 #else (#symInt("FinalTime") -Int #symInt("Time")) divInt 10 #fi +Int 3 *Int #if #symInt("Time2") -Int #symInt("Time") <=Int 3 #then (#symInt("FinalTime") -Int #symInt("Time")) cdivInt 15 #else (#symInt("FinalTime") -Int #symInt("Time")) divInt 15 #fi +Int (3 *Int (#symInt("N"))) +Int 1 andBool #symInt("FinalTime1") >Int #symInt("FinalTime") andBool #symInt("FinalTime2") >Int #symInt("FinalTime") </rformula>
      <rfreevars> SetItem(#symInt("FinalTime1")) SetItem(#symInt("FinalTime2")) SetItem(#symInt("FinalTime")) </rfreevars>
    </rhs>
  </rhss>
</task>
