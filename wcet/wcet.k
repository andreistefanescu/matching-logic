require "lib/matching-logic.k"

module WCET
  imports MATCHING-LOGIC

  syntax BInst ::= BOpCode Register "," Exp "," Exp [klabel('binst), strict(3, 4)]
  syntax BOpCode ::= "add" | "sub" | "mul" | "div" | "or" | "and"
  syntax Exp ::= Register
               | "#" Int
               | Int
  syntax Register ::= "r" Int
  syntax UInst ::= UOpCode Register "," Exp [klabel('uinst), strict(3)]
  syntax UOpCode ::= "not" | "load" | "li"
  syntax MInst ::= MOpCode Exp "," Exp [klabel('minst), strict(2, 3)]
  syntax MOpCode ::= "store"
  syntax JInst ::= JOpCode Id [klabel('jinst)]
  syntax JOpCode ::= "jmp"
  syntax BrInst ::= BrOpCode Id "," Exp "," Exp [klabel('brinst), strict(3, 4)]
  syntax BrOpCode ::= "beq" | "bne" | "blt" | "ble" | "bgt" | "bge"

  syntax NInst ::= NOpCode [klabel('ninst)]
  syntax NOpCode ::= "halt"

  syntax SInst ::= SOpCode Exp [klabel('sinst), strict(2)]
  syntax SOpCode ::= "sleep"

  syntax RInst ::= ROpCode Register "," Id [klabel('rinst)]
  syntax ROpCode ::= "read"

  syntax WInst ::= WOpCode Id "," Exp [klabel('winst), strict(3)]
  syntax WOpCode ::= "write"

  syntax RWInst ::= RWOpCode Register "," Id "," Exp [klabel('rwinst), strict(4)]
  syntax RWOpCode ::= "rw"

  syntax Inst ::= BInst | UInst | MInst | JInst | BrInst | NInst | SInst | RInst | WInst | RWInst
  syntax Insts ::= Inst | Inst Insts
  syntax Block ::= Id ":" Insts
  syntax Blocks ::= Block | Block Blocks

  syntax OpCode ::= BOpCode | UOpCode | MOpCode | JOpCode | BrOpCode | NOpCode | SOpCode | ROpCode | WOpCode | RWOpCode

/*
  configuration
    <T>
      <k> load($PGM:K) ~> jumpToMain </k>
      <pgm> .Map </pgm>
      <mem> .Map </mem>
      <reg> .Map </reg>
      <timing> $TIMING:Map </timing>
      <wcet> 0 </wcet>
    </T>
*/

  //TODO: remove
  configuration
      <tasks>
        <task multiplicity="*">
          <lhs>
            <config>
              <T>
                <k> .K </k>
                <pgm> .Map </pgm>
                <mem> .Map </mem>
                <reg> .Map </reg>
                <timing> .Map </timing>
                <wcet> 0 </wcet>
                <input> .List </input>
                <status> .Map </status>
              </T>
            </config>
            <formula> true </formula>
            <progress> false </progress>
          </lhs>
          <rhss>
            <rhs multiplicity="*">
              <rconfig> .Bag </rconfig>
              <rformula> true </rformula>
              <rfreevars> .Set </rfreevars>
            </rhs>
          </rhss>      
        </task>
        $PGM:Bag
      </tasks>

  syntax KResult ::= Int

  syntax K ::= load(K)
             | "jumpToMain"

  rule <k> load(B:Block Bs:Blocks) => load(B) ~> load(Bs) ...</k>
       <progress> _ => true </progress>
  rule <k> load(X:Id : Is:Insts) => . ...</k>
       <pgm>... . => X |-> (Is) ...</pgm>
       <progress> _ => true </progress>
  rule <k> I:Inst Is:Insts => I ~> Is ...</k>
       <progress> _ => true </progress>

  rule <k> jumpToMain => K </k>
       <pgm>... X:Id |-> K ...</pgm>
       <progress> _ => true </progress> when Id2String(X) ==String "main"

  rule <k> r I:Int => I2:Int ...</k>
       <reg>... I |-> I2 ...</reg>
       <progress> _ => true </progress>
  rule <k> # I:Int => I ...</k>
       <progress> _ => true </progress>

  rule <k> add r I:Int , I2:Int , I3:Int => time(add) ...</k>
       <reg> R:Map => R[I2 +Int I3 / I] </reg>
       <progress> _ => true </progress>
  rule <k> sub r I:Int , I2:Int , I3:Int => time(sub) ...</k>
       <reg> R:Map => R[I2 -Int I3 / I] </reg>
       <progress> _ => true </progress>
  rule <k> mul r I:Int , I2:Int , I3:Int => time(mul) ...</k>
       <reg> R:Map => R[I2 *Int I3 / I] </reg>
       <progress> _ => true </progress>
  rule <k> div r I:Int , I2:Int , I3:Int => time(div) ...</k>
       <reg> R:Map => R[I2 /Int I3 / I] </reg>
       <progress> _ => true </progress>
  rule <k> or r I:Int , I2:Int , I3:Int => time(or) ...</k>
       <reg> R:Map => R[I2 |Int I3 / I] </reg>
       <progress> _ => true </progress>
  rule <k> and r I:Int , I2:Int , I3:Int => time(and) ...</k>
       <reg> R:Map => R[I2 &Int I3 / I] </reg>
       <progress> _ => true </progress>

  rule <k> not r I , I2:Int => time(not) ...</k>
       <reg> R:Map => R[~Int I2 / I] </reg>
       <progress> _ => true </progress>
  rule <k> load r I:Int , I2:Int => time(load) ...</k>
       <mem>... I2 |-> I3:Int ...</mem>
       <reg> R:Map => R[I3 / I] </reg>
       <progress> _ => true </progress>
  rule li R , E => or R , E , #0 [macro]

  rule <k> store I:Int , I2:Int => time(store) ...</k>
       <mem> M:Map => M[I2 / I] </mem>
       <progress> _ => true </progress>

  rule <k> jmp X:Id => time(jmp) ~> K</k>
       <pgm>... X |-> K ...</pgm>
       <progress> _ => true </progress>

  rule <k> beq X:Id , I:Int , I2:Int => time(beq) ~> branch(I ==Int I2, X)  ...</k>
       <progress> _ => true </progress>
  rule <k> bne X:Id , I:Int , I2:Int => time(bne) ~> branch(I =/=Int I2, X) ...</k>
       <progress> _ => true </progress>
  rule <k> blt X:Id , I:Int , I2:Int => time(blt) ~> branch(I <Int I2, X) ...</k>
       <progress> _ => true </progress>
  rule <k> ble X:Id , I:Int , I2:Int => time(ble) ~> branch(I <=Int I2, X) ...</k>
       <progress> _ => true </progress>
  rule bgt X , E , E2 => blt X , E2 , E [macro]
  rule bge X , E , E2 => ble X , E2 , E [macro]

  syntax K ::= branch(Bool, Id)
/*
  rule <k> branch(true, X:Id) => Pgm(X) ...</k>
       <pgm> Pgm:Map </pgm>
  rule <k> branch(false, _) => . ...</k>
*/

  //TODO: remove
  rule [branch]: <task>
         <lhs>
         <config><T>
           <k> branch(B:Bool, X:Id) ~> K </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </T></config>
         <formula> Phi </formula>
         <progress> _ </progress></lhs>
         Task:Bag
       </task>
       =>
       <task><lhs>
         <config><T>
           <k> Pgm(X) </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </T></config>
         <formula> Phi andBool (B ==Bool true) </formula>
         <progress> true </progress></lhs>
         Task:Bag
       </task>
       <task><lhs>
         <config><T>
           <k> K </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </T></config>
         <formula> Phi andBool (B ==Bool false) </formula>
         <progress> true </progress></lhs>
         Task:Bag
       </task>
       
  rule <k> halt ~> _ => time(halt) </k>
       <progress> _ => true </progress>

  rule <k> sleep I:Int => waitFor(I) ...</k>
       <progress> _ => true </progress>

  rule <k> read r I:Int , X:Id => time(read) ...</k>
       <status>... X |-> I2 ...</status>
       <reg> Reg:Map => Reg[I2 / I] </reg>
       <progress> _ => true </progress>

  rule <k> write X:Id , I:Int => time(write) ...</k>
       <status> Status:Map => Status[I / X] </status>
       <progress> _ => true </progress>

  rule <k> rw r I:Int , X:Id , I3:Int => time(rw) ...</k>
       <status>... X |-> (I2 => I3) ...</status>
       <reg> Reg:Map => Reg[I2 / I] </reg>
       <progress> _ => true </progress>

  syntax K ::= time(OpCode)
  rule <k> time(O:OpCode) => waitFor(Timing(O)) ...</k>
       <timing> Timing:Map </timing>
       <progress> _ => true </progress>

  syntax K ::= waitFor(Int)

  rule <k> waitFor(I:Int) => updateStatus(I2) ...</k>
       <wcet> I2:Int => I2 +Int I </wcet>
       <progress> _ => true </progress>

  syntax K ::= updateStatus(Int)
  syntax K ::= (Int, Map)

/*
  rule <k> updateStatus(Start) => . ...</k>
       <input> ListItem((I2:Int, M)) ...</input>
       <wcet> I:Int </wcet>
       <status> Status:Map => Status[M] </status> when I >=Int I2 andBool I2 >=Int Start

  rule <k> updateStatus(Start) => . ...</k>
       <input> ListItem((I2:Int, M)) ...</input>
       <wcet> I:Int </wcet> when notBool(I >=Int I2 andBool I >=Int Start)
*/

  rule [updateStatus]:
    <task><lhs>
      <config><T>
        <k> updateStatus(Start) ~> K </k>
        <input> ListItem((I2:Int, M)) Input:List </input>
        <wcet> I:Int </wcet>
        <status> Status:Map </status>
        Cfg:Bag
      </T></config>
      <formula> Phi </formula>
      <progress> _ </progress></lhs>
      Task:Bag
    </task>
    =>
    <task><lhs>
      <config><T>
        <k> K </k>
        <input> Input </input>
        <wcet> I </wcet>
        <status> Status[M] </status>
        Cfg
      </T></config>
      <formula> Phi andBool I >=Int I2 andBool I2 >=Int Start </formula>
      <progress> true </progress></lhs>
      Task
    </task>
    <task><lhs>
      <config><T>
        <k> K </k>
        <input> ListItem((I2, M)) Input </input>
        <wcet> I </wcet>
        <status> Status </status>
        Cfg
      </T></config>
      <formula> Phi andBool notBool(I >=Int I2 andBool I2 >=Int Start) </formula>
      <progress> true </progress></lhs>
      Task
    </task>

  rule <k> updateStatus(_) => . ...</k>
       <input> .List </input>
       <progress> _ => true </progress>

endmodule
