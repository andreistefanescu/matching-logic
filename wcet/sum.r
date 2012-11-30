<task>
  <lhs>
    <config>
      <T>
        <k> add r 2 , r 2 , #1
            add r 1 , r 1 , r 2
            bne sum , r 2 , r 0
            halt </k>
        <pgm> main |-> li r 0 , #10
                       li r 1 , #0
                       li r 2 , #0
                       jmp sum
              sum |-> add r 2 , r 2 , #1
                      add r 1 , r 1 , r 2
                      bne sum , r 2 , r 0
                      halt </pgm>
        <mem> #symMap(1) </mem>
        <reg> 0 |-> #symInt(2) 1 |-> #symInt(3) 2 |-> #symInt(4) </reg>
        <timing> #symMap(5) </timing>
        <wcet> #symInt(6) </wcet>
      </T>
    </config>
    <formula> #symInt(3) ==Int (#symInt(4) *Int (#symInt(4) +Int 1) /Int 2) </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> halt </k>
          <pgm> main |-> li r 0 , #10
                         li r 1 , #0
                         li r 2 , #0
                         jmp sum
                sum |-> add r 2 , r 2 , #1
                        add r 1 , r 1 , r 2
                        bne sum , r 2 , r 0
                        halt </pgm>
          <reg> 0 |-> #symInt(2) 1 |-> (#symInt(2) *Int (#symInt(2) +Int 1) /Int 2) 2 |-> #symInt(2) </reg>
        </T>
      </rconfig>
      <rformula> true </rformula>
    </rhs>
  </rhss>
</task>
