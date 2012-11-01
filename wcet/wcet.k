module WCET

  syntax BInst ::= BOpCode Register "," Exp "," Exp [strict(3 4)]
  syntax BOpCode ::= "add" | "sub" | "mul" | "div" | "or" | "and"
  syntax Exp ::= Register
               | "#" Int
  syntax Register ::= "r" Int
  syntax UInst ::= UOpCode Register "," Exp
  syntax UOpCode ::= "not" | "load" | "li"
  syntax MInst ::= MOpCode Exp "," Exp
  syntax MOpCode ::= "store"
  syntax JInst ::= JOpCode Id
  syntax JOpCode ::= "jmp"
  syntax BrInst ::= BrOpCode Id "," Exp "," Exp [strict(3 4)]
  syntax BrOpCode ::= "beq" | "bne" | "blt" | "ble" | "bgt" | "bge"

  syntax NInst ::= NOpCode
  syntax NOpCode ::= "halt"

  syntax Inst ::= BInst | UInst | MInst | JInst | BrInst | NInst
  syntax Insts ::= Inst | Inst Insts
  syntax Block ::= Id ":" Insts
  syntax Blocks ::= Block | Block Blocks

  syntax OpCode ::= BOpCode | UOpCode | MOpCode | JOpCode | BrOpCode | NOpCode

  configuration
    <top>
      <tasks>
        <task multiplicity="*">
          <lhs>
            <config>
              <T>
                <k> .K </k>
                <pgm> .Map </pgm>
                <mem> .Map </mem>
                <reg> .Map </reg>
                <timing> $TIMING:Map </timing>
                <wcet> 0 </wcet>
              </T>
            </config>
            <formula> true </formula>
            <progress> false </progress>
          </lhs>
          <rhss>
            <rhs multiplicity="*">
              <config> .Bag </config>
              <formula> true </formula>
            </rhs>
          </rhss>      
        </task>
        $PGM:Bag
      </tasks>
    </top>

  syntax KResult ::= Int

  context M:MOpCode HOLE , _
  context M:MOpCode _ , HOLE
  context U:UOpCode _ , HOLE

  syntax K ::= load( K )
             | "jumpToMain"

  rule <top>... <k> load(B:Block Bs:Blocks) => load(B) ~> load(Bs) ...</k><progress> _ => true </progress> ...</top>
  rule <top>... <k> load(X:Id : Is:Insts) => . ...</k>
       <pgm>... . => X |-> (Is) ...</pgm><progress> _ => true </progress> ...</top>
  rule <top>... <k> I:Inst Is:Insts => I ~> Is ...</k><progress> _ => true </progress> ...</top>

  rule <top>... <k> jumpToMain => K </k>
       <pgm>... X:Id |-> K ...</pgm><progress> _ => true </progress> ...</top> when Id2String(X) ==String "main"

  rule <top>... <k> r I:Int => I2:Int ...</k>
       <reg>... I |-> I2 ...</reg><progress> _ => true </progress> ...</top>
  rule <top>... <k> # I:Int => I ...</k><progress> _ => true </progress> ...</top>

  rule <top>... <k> add r I:Int , I2:Int , I3:Int => time(add) ...</k>
       <reg> R:Map => R[I2 +Int I3 / I] </reg><progress> _ => true </progress> ...</top>
  rule <top>... <k> sub r I:Int , I2:Int , I3:Int => time(sub) ...</k>
       <reg> R:Map => R[I2 -Int I3 / I] </reg><progress> _ => true </progress> ...</top>
  rule <top>... <k> mul r I:Int , I2:Int , I3:Int => time(mul) ...</k>
       <reg> R:Map => R[I2 *Int I3 / I] </reg><progress> _ => true </progress> ...</top>
  rule <top>... <k> div r I:Int , I2:Int , I3:Int => time(div) ...</k>
       <reg> R:Map => R[I2 /Int I3 / I] </reg><progress> _ => true </progress> ...</top>
  rule <top>... <k> or r I:Int , I2:Int , I3:Int => time(or) ...</k>
       <reg> R:Map => R[I2 |Int I3 / I] </reg><progress> _ => true </progress> ...</top>
  rule <top>... <k> and r I:Int , I2:Int , I3:Int => time(and) ...</k>
       <reg> R:Map => R[I2 &Int I3 / I] </reg><progress> _ => true </progress> ...</top>

  rule <top>... <k> not r I , I2:Int => time(not) ...</k>
       <reg> R:Map => R[~Int I2 / I] </reg><progress> _ => true </progress> ...</top>
  rule <top>... <k> load r I:Int , I2:Int => time(load) ...</k>
       <mem>... I2 |-> I3:Int ...</mem>
       <reg> R:Map => R[I3 / I] </reg><progress> _ => true </progress> ...</top>
  rule li R , E => or R , E , #0 [macro]

  rule <top>... <k> store I:Int , I2:Int => time(store) ...</k>
       <mem> M:Map => M[I2 / I] </mem><progress> _ => true </progress> ...</top>

  rule <top>... <k> jmp X:Id => time(jmp) ~> K</k>
       <pgm>... X |-> K ...</pgm><progress> _ => true </progress> ...</top>

  rule <top>... <k> beq X:Id , I:Int , I2:Int => time(beq) ~> branch(I ==Int I2, X)  ...</k><progress> _ => true </progress> ...</top>
  rule <top>... <k> bne X:Id , I:Int , I2:Int => time(bne) ~> branch(I =/=Int I2, X) ...</k><progress> _ => true </progress> ...</top>
  rule <top>... <k> blt X:Id , I:Int , I2:Int => time(blt) ~> branch(I <Int I2, X) ...</k><progress> _ => true </progress> ...</top>
  rule <top>... <k> ble X:Id , I:Int , I2:Int => time(ble) ~> branch(I <=Int I2, X) ...</k><progress> _ => true </progress> ...</top>
  rule bgt X , E , E2 => blt X , E2 , E [macro]
  rule bge X , E , E2 => ble X , E2 , E [macro]

  syntax K ::= "branch" "(" Bool "," Id ")"
  rule <top>... <k> branch(B:Bool, X:Id) => Pgm(X) ...</k>
       <pgm> Pgm:Map </pgm>
       <formula> Phi => Phi andBool B ==Bool true </formula><progress> _ => true </progress> ...</top> when checkSat(notBool (Phi impliesBool B ==Bool true)) ==K unsat [structural]
  rule <top>... <k> branch(B:Bool, _) => . ...</k>
       <formula> Phi => Phi andBool B ==Bool false </formula><progress> _ => true </progress> ...</top> when checkSat(notBool (Phi impliesBool B ==Bool false)) ==K unsat [structural]
  rule <top>... <task>
         <config>
           <k> branch(B:Bool, X:Id) ~> K </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </config>
         <formula> Phi </formula>
         <progress> _ </progress>
         Task:Bag
       </task>
       =>
       <task>
         <config>
           <k> Pgm(X) ~> K </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </config>
         <formula> Phi andBool B ==Bool true </formula>
         <progress> true </progress>
         Task:Bag
       </task>
       <task>
         <config>
           <k> K </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </config>
         <formula> Phi andBool B ==Bool false </formula>
         <progress> true </progress>
         Task:Bag
       </task> ...</top>
       
  rule <top>... <k> halt ~> _ => time(halt) </k><progress> _ => true </progress> ...</top>

  syntax K ::= "time" "(" OpCode ")"
  rule <top>... <k> time(O:OpCode) => . ...</k>
       <timing>... O |-> I:Int ...</timing>
       <wcet> I2:Int => I2 +Int I </wcet><progress> _ => true </progress> ...</top> [structural]

endmodule
