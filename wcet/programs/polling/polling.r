<task>
  <lhs>
    <config>
      <T>
        <k> read r 1 , data , #0
            load r 2 , #0
            add r 2 , r 2 , r 1
            store #0, r 2
            sub r 0 , r 0 , #1
            bne loop , r 0 , #0
            halt </k>
        <pgm> 
          main |-> store #0, #0
                   or r 0 , #100 , #0
                   jmp loop
          loop |-> read r 1 , data , #0
                   load r 2 , #0
                   add r 2 , r 2 , r 1
                   store #0, r 2
                   sub r 0 , r 0 , #1
                   bne loop , r 0 , #0
                   halt </pgm>
        <reg> 0 |-> #symInt("N") 1 |-> #symInt(0) 2 |-> #symInt(1) </reg>
        <mem> 0 |-> #symInt("Sum") </mem>
        <status> data |-> #symInt("Data") </status>
        <input> #symInt("Time1") |-> Map2KLabel data |-> #symInt("Data1")(.List{K}) #symInt("Time2") |-> Map2KLabel data |-> #symInt("Data2")(.List{K}) </input>
        <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 </timing>
        <wcet> #symInt("Time") </wcet>
      </T>
    </config>
    <formula> #symInt("Time1") -Int #symInt("Time") >Int 34 andBool #symInt("Time2") -Int #symInt("Time") >Int 34 </formula>
    <progress> false </progress>
  </lhs>
  <rhss>
    <rhs>
      <rconfig>
        <T>
          <k> halt </k>
          <pgm> 
            main |-> store #0, #0
                     or r 0 , #100 , #0
                     jmp loop
            loop |-> read r 1 , data , #0
                     load r 2 , #0
                     add r 2 , r 2 , r 1
                     store #0, r 2
                     sub r 0 , r 0 , #1
                     bne loop , r 0 , #0
                     halt </pgm>
          <reg> 0 |-> 0 1 |-> #symInt("Data2") 2 |-> #symInt("Sum") +Int #symInt("Data") +Int #symInt("Data1") +Int #symInt("Data2") </reg>
          <mem> 0 |-> #symInt("Sum") +Int #symInt("Data") +Int #symInt("Data1") +Int #symInt("Data2") </mem>
          <status> data |-> 0 </status>
          <input> #symInt("Time1") |-> Map2KLabel data |-> #symInt("Data1")(.List{K}) #symInt("Time2") |-> Map2KLabel data |-> #symInt("Data2")(.List{K}) </input>
          <timing> add |-> 1 sub |-> 1 mul |-> 1 div |-> 1 or |-> 1 and |-> 1 not |-> 1 load |-> 10 store |-> 10 jmp |-> 1 beq |-> 2 bne |-> 2 blt |-> 2 ble |-> 2 halt |-> 1 read |-> 10 </timing>
          <wcet> #symInt(4) </wcet>
        </T>     
      </rconfig>
      <rformula> true </rformula>
    </rhs>
  </rhss>
</task>
