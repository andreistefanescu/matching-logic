<task>
  <lhs>
    <config>
      <T>
        <k> load(
main:	li r 0 , # #symInt("N")
	li r 1 , #0
	li r 2 , #0
	jmp sum
sum:	add r 2 , r 2 , #1
	add r 1 , r 1 , r 2
	bne sum , r 2 , r 0
	halt
) ~> jumpTo(main) </k>
        <pgm> .Map </pgm>
        <mem> .Map </mem>
        <reg> .Map </reg>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 </timing>
        <wcet> 0 </wcet>
        <input> .List </input>
        <status> .Map </status>
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
          <pgm> main |-> li r 0 , # #symInt("N")
                         li r 1 , #0
                         li r 2 , #0
                         jmp sum
                sum |-> add r 2 , r 2 , #1
                        add r 1 , r 1 , r 2
                        bne sum , r 2 , r 0
                        halt </pgm>
          <mem> .Map </mem>
          <status> .Map </status>
          <input> .List </input>
          <reg> 0 |-> #symInt("N") 1 |-> #symInt("N") *Int (#symInt("N") +Int 1) divInt 2  2 |-> #symInt("N") </reg>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 </timing>
          <wcet> 5 +Int 4 *Int #symInt("N") </wcet>
          <timers> .List </timers>
          <priority> 0 </priority>
          <stack> .List </stack>
          <interrupts> .Set </interrupts>
        </T>
      </rconfig>
      <rformula> true </rformula>
      <rfreevars> .Set </rfreevars>
    </rhs>
  </rhss>
</task>
<task>
  <lhs>
    <config>
      <T>
        <k> add r 2 , r 2 , #1
            add r 1 , r 1 , r 2
            bne sum , r 2 , r 0
            halt </k>
        <pgm> main |-> li r 0 , # #symInt("_")
                       li r 1 , #0
                       li r 2 , #0
                       jmp sum
              sum |-> add r 2 , r 2 , #1
                      add r 1 , r 1 , r 2
                      bne sum , r 2 , r 0
                      halt </pgm>
        <mem> .Map </mem>
        <status> .Map </status>
        <input> .List </input>
        <reg> 0 |-> #symInt("N") 1 |-> #symInt("S") 2 |-> #symInt("I") </reg>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 </timing>
        <wcet> #symInt("Time") </wcet>
        <timers> .List </timers>
        <priority> 0 </priority>
        <stack> .List </stack>
        <interrupts> .Set </interrupts>
      </T>
    </config>
    <formula> #symInt("S") ==Int (#symInt("I") *Int (#symInt("I") +Int 1) divInt 2) </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> .K </k>
          <pgm> main |-> li r 0 , # #symInt("_")
                         li r 1 , #0
                         li r 2 , #0
                         jmp sum
                sum |-> add r 2 , r 2 , #1
                        add r 1 , r 1 , r 2
                        bne sum , r 2 , r 0
                        halt </pgm>
          <mem> .Map </mem>
          <status> .Map </status>
          <input> .List </input>
          <reg> 0 |-> #symInt("N") 1 |-> (#symInt("N") *Int (#symInt("N") +Int 1) divInt 2) 2 |-> #symInt("N") </reg>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 </timing>
          <wcet> #symInt("Time") +Int (#symInt("N") -Int #symInt("I")) *Int 4 +Int 1 </wcet>
          <timers> .List </timers>
          <priority> 0 </priority>
          <stack> .List </stack>
          <interrupts> .Set </interrupts>
        </T>
      </rconfig>
      <rformula> true </rformula>
      <rfreevars> .Set </rfreevars>
    </rhs>
  </rhss>
</task>
