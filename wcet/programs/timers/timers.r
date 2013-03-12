<task>
  <lhs>
    <config>
      <T>
        <k> load(

main:	li r 0 , # #symInt("N")
	li r 1 , #0
	li r 2 , #0
	int t1, # #symInt("Time1"), #10
	int t2, # #symInt("Time2"), #15
	jmp loop
loop:	sub r 0 , r 0 , #1
	bne loop , r 0 , #0
	halt
t1:	add r 1 , r 1 , #1
	rfi
t2:	add r 2 , r 2 , #1
	rfi
) ~> jumpTo(main) </k>
        <pgm> .Map </pgm>
        <mem> .Map </mem>
        <reg> .Map </reg>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 int |-> 2 rfi |-> 2 </timing>
        <wcet> 0 </wcet>
        <input> .List </input>
        <status> .Map </status>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
      </T>
    </config>
    <formula> #symInt("N") >Int 0 andBool #symInt("Time1") >Int 5 andBool #symInt("Time2") >Int 3 </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> .K </k>
          <pgm>
            main |-> or r 0 , # #symInt("N") , #0
                     or r 1 , #0 , #0
                     or r 2 , #0 , #0
                     int t1 , # #symInt("Time1") , #10
                     int t2 , # #symInt("Time2") , #15
                     jmp loop
            loop |-> sub r 0 , r 0 , #1
                     bne loop , r 0 , #0
                     halt
            t1 |-> add r 1 , r 1 , #1
                   rfi
            t2 |-> add r 2 , r 2 , #1
                   rfi
          </pgm>
          <reg> 0 |-> 0 1 |-> maxInt(0, (#symInt("Duration") -Int #symInt("Time1") +Int 5) cdivInt 10) 2 |-> maxInt(0, (#symInt("Duration") -Int #symInt("Time2") +Int 3) cdivInt 15) </reg>
          <mem> .Map </mem>
          <status> .Map </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 int |-> 2 rfi |-> 2 </timing>
          <wcet> 8 +Int #symInt("Duration") </wcet>
          <timers> ListItem((t1 , #symInt("GeneratedFreshVar0") , 10))
                   ListItem((t2 , #symInt("GeneratedFreshVar1") , 15))
          </timers>
          <priority> 0 </priority>
          <stack> .List </stack>
          <interrupts> .Set </interrupts>
        </T>
      </rconfig>
      <rformula> #symInt("Duration") ==Int 3 *Int #symInt("N") +Int 1 +Int maxInt(0, 3 *Int ((#symInt("Duration") -Int #symInt("Time1") +Int 5) cdivInt 10)) +Int maxInt(0, 3 *Int ((#symInt("Duration") -Int #symInt("Time2") +Int 3) cdivInt 15)) andBool #symInt("Duration") >Int 0 </rformula>
      <rfreevars> SetItem(#symInt("Duration")) SetItem(#symInt("GeneratedFreshVar0")) SetItem(#symInt("GeneratedFreshVar1")) </rfreevars>
    </rhs>
  </rhss>
</task>
<task>
  <lhs>
    <config>
      <T>
        <k> sub r 0 , r 0 , #1
            bne loop , r 0 , #0
            halt </k>
        <pgm>
          main |-> or r 0 , # #symInt("_1") , #0
                   or r 1 , #0 , #0
                   or r 2 , #0 , #0
                   int t1 , # #symInt("_2") , #10
                   int t2 , # #symInt("_3") , #15
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
            main |-> or r 0 , # #symInt("_1") , #0
                     or r 1 , #0 , #0
                     or r 2 , #0 , #0
                     int t1 , # #symInt("_2") , #10
                     int t2 , # #symInt("_3") , #15
                     jmp loop
            loop |-> sub r 0 , r 0 , #1
                     bne loop , r 0 , #0
                     halt
            t1 |-> add r 1 , r 1 , #1
                   rfi
            t2 |-> add r 2 , r 2 , #1
                   rfi
          </pgm>
          <reg> 0 |-> 0 1 |-> #symInt("T1") +Int maxInt(0, (#symInt("Duration") -Int #symInt("Time1") +Int #symInt("Time")) cdivInt 10) 2 |-> #symInt("T2") +Int maxInt(0, (#symInt("Duration") -Int #symInt("Time2") +Int #symInt("Time")) cdivInt 15) </reg>
          <mem> .Map </mem>
          <status> .Map </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 int |-> 2 rfi |-> 2 </timing>
          <wcet> #symInt("Time") +Int #symInt("Duration") </wcet>
          <timers> ListItem((t1 , #symInt("GeneratedFreshVar0") , 10))
                   ListItem((t2 , #symInt("GeneratedFreshVar1") , 15))
          </timers>
          <priority> 0 </priority>
          <stack> .List </stack>
          <interrupts> .Set </interrupts>
        </T>
      </rconfig>
      <rformula> #symInt("Duration") ==Int 3 *Int #symInt("N") +Int 1 +Int maxInt(0, 3 *Int ((#symInt("Duration") -Int #symInt("Time1") +Int #symInt("Time")) cdivInt 10)) +Int maxInt(0, 3 *Int ((#symInt("Duration") -Int #symInt("Time2") +Int #symInt("Time")) cdivInt 15)) andBool #symInt("Duration") >Int 0 </rformula>
      <rfreevars> SetItem(#symInt("Duration")) SetItem(#symInt("GeneratedFreshVar0")) SetItem(#symInt("GeneratedFreshVar1")) </rfreevars>
    </rhs>
  </rhss>
</task>
