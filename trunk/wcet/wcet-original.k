module WCET

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

  syntax RInst ::= ROpCode Register "," Id "," Exp [klabel('rinst), strict(4)]
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

  configuration
    <T>
      <k> load($PGM:K) ~> jumpToMain </k>
      <pgm> .Map </pgm>
      <mem> .Map </mem>
      <reg> .Map </reg>
      <timing> $TIMING:Map </timing>
      <wcet> 0 </wcet>
      <input> $INPUT:List </input>
      <status> $INITIAL:Map </status>
    </T>

  syntax KResult ::= Int

  syntax K ::= load(K)
             | "jumpToMain"

  rule <k> load(B:Block Bs:Blocks) => load(B) ~> load(Bs) ...</k>
  rule <k> load(X:Id : Is:Insts) => . ...</k>
       <pgm>... . => X |-> (Is) ...</pgm>
  rule <k> I:Inst Is:Insts => I ~> Is ...</k>

  rule <k> jumpToMain => K </k>
       <pgm>... X:Id |-> K ...</pgm>
        when Id2String(X) ==String "main"

  rule <k> r I:Int => I2:Int ...</k>
       <reg>... I |-> I2 ...</reg>
  rule <k> # I:Int => I ...</k>

  rule <k> add r I:Int , I2:Int , I3:Int => time(add) ...</k>
       <reg> R:Map => R[I2 +Int I3 / I] </reg>
  rule <k> sub r I:Int , I2:Int , I3:Int => time(sub) ...</k>
       <reg> R:Map => R[I2 -Int I3 / I] </reg>
  rule <k> mul r I:Int , I2:Int , I3:Int => time(mul) ...</k>
       <reg> R:Map => R[I2 *Int I3 / I] </reg>
  rule <k> div r I:Int , I2:Int , I3:Int => time(div) ...</k>
       <reg> R:Map => R[I2 /Int I3 / I] </reg>
  rule <k> or r I:Int , I2:Int , I3:Int => time(or) ...</k>
       <reg> R:Map => R[I2 |Int I3 / I] </reg>
  rule <k> and r I:Int , I2:Int , I3:Int => time(and) ...</k>
       <reg> R:Map => R[I2 &Int I3 / I] </reg>

  rule <k> not r I , I2:Int => time(not) ...</k>
       <reg> R:Map => R[~Int I2 / I] </reg>
  rule <k> load r I:Int , I2:Int => time(load) ...</k>
       <mem>... I2 |-> I3:Int ...</mem>
       <reg> R:Map => R[I3 / I] </reg>
  rule li R , E => or R , E , #0 [macro]

  rule <k> store I:Int , I2:Int => time(store) ...</k>
       <mem> M:Map => M[I2 / I] </mem>

  rule <k> jmp X:Id => time(jmp) ~> K</k>
       <pgm>... X |-> K ...</pgm>

  rule <k> beq X:Id , I:Int , I2:Int => time(beq) ~> branch(I ==Int I2, X)  ...</k>
  rule <k> bne X:Id , I:Int , I2:Int => time(bne) ~> branch(I =/=Int I2, X) ...</k>
  rule <k> blt X:Id , I:Int , I2:Int => time(blt) ~> branch(I <Int I2, X) ...</k>
  rule <k> ble X:Id , I:Int , I2:Int => time(ble) ~> branch(I <=Int I2, X) ...</k>
  rule bgt X , E , E2 => blt X , E2 , E [macro]
  rule bge X , E , E2 => ble X , E2 , E [macro]

  syntax K ::= branch(Bool, Id)

  rule <k> branch(true, X:Id) => Pgm(X) ...</k>
       <pgm> Pgm:Map </pgm>
  rule <k> branch(false, _) => . ...</k>

  rule <k> halt ~> _ => time(halt) </k>

  rule <k> sleep I:Int => waitFor(I) ...</k>

  rule <k> read r I:Int , X:Id => time(read) ...</k>
       <status>... X |-> I2 ...</status>
       <reg> Reg:Map => Reg[I2 / I] </reg>

  rule <k> write X:Id , I:Int => time(write) ...</k>
       <status> Status:Map => Status[I / X] </status>

  rule <k> rw r I:Int , X:Id , I3:Int => time(rw) ...</k>
       <status>... X |-> (I2 => I3) ...</status>
       <reg> Reg:Map => Reg[I2 / I] </reg>

  syntax K ::= time(OpCode)
  rule <k> time(O:OpCode) => waitFor(Timing(O)) ...</k>
       <timing> Timing:Map </timing>

  syntax K ::= waitFor(Int)
  rule <k> waitFor(I:Int) => updateStatus(I2) ...</k>
       <wcet> I2:Int => I2 +Int I </wcet> 

  syntax K ::= updateStatus(Int)
  syntax ListItem ::= (Int, Map)

  rule <k> updateStatus(Start) => . ...</k>
       <input> (I2:Int, M) => . ...</input>
       <wcet> I:Int </wcet>
       <status> Status:Map => Status[M] </status> when I >=Int I2 andBool I2 >=Int Start

  rule <k> updateStatus(Start) => . ...</k>
       <input> (I2:Int, M) ...</input>
       <wcet> I:Int </wcet> when notBool(I >=Int I2 andBool I >=Int Start)

  rule <k> updateStatus(_) => . ...</k>
       <input> .List </input>

endmodule
