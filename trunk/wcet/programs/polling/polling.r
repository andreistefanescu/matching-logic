<task>
  <lhs>
    <config>
      <T>
        <k> load(
main:	store #0, #0
	li r 0 , # #symInt("N")
        li r 1 , #0
        li r 2 , #0
	jmp loop
loop:	rw r 1, data , #0
	load r 2 , #0
	add r 2 , r 2 , r 1
	store #0, r 2
	sub r 0 , r 0 , #1
	bne loop , r 0 , #0
	halt
) ~> jumpTo(main) </k>
        <pgm> .Map </pgm>
        <mem> .Map </mem>
        <reg> .Map </reg>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6 </timing>
        <wcet> 0 </wcet>
        <input> ListItem((#symInt("Time1"), data |-> #symInt("Data1"))) ListItem((#symInt("Time2"), data |-> #symInt("Data2"))) </input>
        <status> data |-> #symInt("Data") </status>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
      </T>
    </config>
    <formula> #symInt("Time2") -Int #symInt("Time1") >Int 16 andBool 0 <Int #symInt("Time1") andBool (#symInt("N") -Int 1) *Int 16 >Int #symInt("Time2") andBool #symInt("Time1") >Int 7 </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> .K </k>
          <pgm> 
            main |-> store #0, #0
                     or r 0 , # #symInt("N") , #0
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
          <reg> 0 |-> 0 1 |-> #symInt("GeneratedFreshVar2") 2 |-> #symInt("GeneratedFreshVar3") </reg>
          <mem> 0 |-> #symInt("Data") +Int #symInt("Data1") +Int #symInt("Data2") </mem>
          <status> data |-> 0 </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6 </timing>
          <wcet> #symInt("N") *Int 16 +Int 8 </wcet>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
        </T>     
      </rconfig>
      <rformula> true </rformula>
      <rfreevars> SetItem(#symInt("GeneratedFreshVar2")) SetItem(#symInt("GeneratedFreshVar3")) </rfreevars>
    </rhs>
  </rhss>
</task>
<task>
  <lhs>
    <config>
      <T>
        <k> rw r 1 , data , #0
            load r 2 , #0
            add r 2 , r 2 , r 1
            store #0, r 2
            sub r 0 , r 0 , #1
            bne loop , r 0 , #0
            halt </k>
        <pgm> 
          main |-> store #0, #0
                   or r 0 , # #symInt("_") , #0
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
        <reg> 0 |-> #symInt("N") 1 |-> #symInt("GeneratedFreshVar0") 2 |-> #symInt("GeneratedFreshVar1") </reg>
        <mem> 0 |-> #symInt("Sum") </mem>
        <status> data |-> #symInt("Data") </status>
        <input> ListItem((#symInt("Time1"), data |-> #symInt("Data1"))) ListItem((#symInt("Time2"), data |-> #symInt("Data2"))) </input>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6 </timing>
        <wcet> #symInt("Time") </wcet>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
      </T>
    </config>
    <formula> #symInt("Time2") -Int #symInt("Time1") >Int 16 andBool #symInt("Time") <Int #symInt("Time1") andBool #symInt("Time") +Int (#symInt("N") -Int 1) *Int 16 >Int #symInt("Time2") </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> .K </k>
          <pgm> 
            main |-> store #0, #0
                     or r 0 , # #symInt("_") , #0
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
          <reg> 0 |-> 0 1 |-> #symInt("GeneratedFreshVar2") 2 |-> #symInt("GeneratedFreshVar3") </reg>
          <mem> 0 |-> #symInt("Sum") +Int #symInt("Data") +Int #symInt("Data1") +Int #symInt("Data2") </mem>
          <status> data |-> 0 </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6 </timing>
          <wcet> #symInt("Time") +Int #symInt("N") *Int 16 +Int 1 </wcet>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
        </T>     
      </rconfig>
      <rformula> true </rformula>
      <rfreevars> SetItem(#symInt("GeneratedFreshVar2")) SetItem(#symInt("GeneratedFreshVar3")) </rfreevars>
    </rhs>
  </rhss>
</task>
<task>
  <lhs>
    <config>
      <T>
        <k> rw r 1 , data , #0
            load r 2 , #0
            add r 2 , r 2 , r 1
            store #0, r 2
            sub r 0 , r 0 , #1
            bne loop , r 0 , #0
            halt </k>
        <pgm> 
          main |-> store #0, #0
                   or r 0 , # #symInt("_") , #0
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
        <reg> 0 |-> #symInt("N") 1 |-> #symInt("GeneratedFreshVar0") 2 |-> #symInt("GeneratedFreshVar1") </reg>
        <mem> 0 |-> #symInt("Sum") </mem>
        <status> data |-> #symInt("Data") </status>
        <input> ListItem((#symInt("Time2"), data |-> #symInt("Data2"))) </input>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6 </timing>
        <wcet> #symInt("Time") </wcet>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
      </T>
    </config>
    <formula> #symInt("Time") <Int #symInt("Time2") andBool #symInt("Time") +Int (#symInt("N") -Int 1) *Int 16 >Int #symInt("Time2") </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> .K </k>
          <pgm> 
            main |-> store #0, #0
                     or r 0 , # #symInt("_") , #0
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
          <reg> 0 |-> 0 1 |-> #symInt("GeneratedFreshVar2") 2 |-> #symInt("GeneratedFreshVar3") </reg>
          <mem> 0 |-> #symInt("Sum") +Int #symInt("Data") +Int #symInt("Data2") </mem>
          <status> data |-> 0 </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6 </timing>
          <wcet> #symInt("Time") +Int #symInt("N") *Int 16 +Int 1 </wcet>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
        </T>     
      </rconfig>
      <rformula> true </rformula>
      <rfreevars> SetItem(#symInt("GeneratedFreshVar2")) SetItem(#symInt("GeneratedFreshVar3")) </rfreevars>
    </rhs>
  </rhss>
</task>
<task>
  <lhs>
    <config>
      <T>
        <k> rw r 1 , data , #0
            load r 2 , #0
            add r 2 , r 2 , r 1
            store #0, r 2
            sub r 0 , r 0 , #1
            bne loop , r 0 , #0
            halt </k>
        <pgm> 
          main |-> store #0, #0
                   or r 0 , # #symInt("_") , #0
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
        <reg> 0 |-> #symInt("N") 1 |-> #symInt("GeneratedFreshVar0") 2 |-> #symInt("GeneratedFreshVar1") </reg>
        <mem> 0 |-> #symInt("Sum") </mem>
        <status> data |-> #symInt("Data") </status>
        <input> .List </input>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6 </timing>
        <wcet> #symInt("Time") </wcet>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
      </T>
    </config>
    <formula> true </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> .K </k>
          <pgm> 
            main |-> store #0, #0
                     or r 0 , # #symInt("_") , #0
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
          <reg> 0 |-> 0 1 |-> #symInt("GeneratedFreshVar2") 2 |-> #symInt("GeneratedFreshVar3") </reg>
          <mem> 0 |-> #symInt("Sum") +Int #symInt("Data") </mem>
          <status> data |-> 0 </status>
          <input> .List </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 3 store |-> 3 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 3 write |-> 3 rw |-> 6 </timing>
          <wcet> #symInt("Time") +Int #symInt("N") *Int 16 +Int 1 </wcet>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
        </T>     
      </rconfig>
      <rformula> true </rformula>
      <rfreevars> SetItem(#symInt("GeneratedFreshVar2")) SetItem(#symInt("GeneratedFreshVar3")) </rfreevars>
    </rhs>
  </rhss>
</task>
