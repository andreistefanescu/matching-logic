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
    <T>
      <tasks>
        <task multiplicity="*">
          <ruleId> .K </rulruleIdd>
          <config>
            <kfrozen> .K </kfrozen>
            <k> .K </k>
            <pgm> .Map </pgm>
            <mem> .Map </mem>
            <reg> .Map </reg>
            <timing> $TIMING:Map </timing>
            <wcet> 0 </wcet>
          </config>
          <formula> true </formula>
          <subst> .Map </subst>
        </task>
      </tasks>
      <rules>
        <rule multiplicity="*">
          <pre> .Bag </pre>
          <posts>
            <post multiplicity="*"> .Bag </post>
          </posts>
          <preform> true </preform>
          <postform> true </postform>
          <id> .K </id>
        </rule>
        $PGM:Bag
      </rules>
    </T>

  syntax KResult ::= Int

  context M:MOpCode HOLE , _
  context M:MOpCode _ , HOLE
  context U:UOpCode _ , HOLE

  syntax K ::= load( K )
             | "jumpToMain"

  rule load(B:Block Bs:Blocks) => load(B) ~> load(Bs)
  rule <k> load(X:Id : Is:Insts) => . ...</k>
       <pgm>... . => X |-> (Is) ...</pgm>
  rule I:Inst Is:Insts => I ~> Is

  rule <k> jumpToMain => K </k>
       <pgm>... X:Id |-> K ...</pgm> when Id2String(X) ==String "main"

  rule <k> r I:Int => I2:Int ...</k>
       <reg>... I |-> I2 ...</reg>
  rule # I:Int => I

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

  rule beq X:Id , I:Int , I2:Int => time(beq) ~> branch(I ==Int I2, X) 
  rule bne X:Id , I:Int , I2:Int => time(bne) ~> branch(I =/=Int I2, X)
  rule blt X:Id , I:Int , I2:Int => time(blt) ~> branch(I <Int I2, X)
  rule ble X:Id , I:Int , I2:Int => time(ble) ~> branch(I <=Int I2, X)
  rule bgt X , E , E2 => blt X , E2 , E [macro]
  rule bge X , E , E2 => ble X , E2 , E [macro]

  syntax K ::= "branch" "(" Bool "," Id ")"
  rule <k> branch(B:Bool, X:Id) => K ...</k>
       <pgm>... X |-> K ...</pgm>
       <formula> Phi </formula> when checkSat(notBool (Phi impliesBool B ==Bool true)) ==K unsat [structural]
  rule branch(B:Bool, _) => . when checkSat(notBool (Phi impliesBool B ==Bool false)) ==K unsat [structural]
  rule <task>
         <config>
           <k> branch(B:Bool, X:Id) ~> K </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </config>
         Task:Bag
       </task>
       =>
       <task>
         <config>
           <k> Pgm(X) ~> K </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </config>
         Task:Bag
       </task>
       <task>
         <config>
           <k> K </k>
           <pgm> Pgm:Map </pgm>
           Cfg:Bag
         </config>
         Task:Bag
       </task>
       
  rule <k> halt ~> _ => time(halt) </k>

  syntax K ::= "time" "(" OpCode ")"
  rule <k> time(O:OpCode) => . ...</k>
       <timing>... O |-> I:Int ...</timing>
       <wcet> I2:Int => I2 +Int I </wcet> [structural]



  rule <rule>
         <pre>
           <kfrozen> K </kfrozen>
           Cfg:Bag
         </pre>
         <preform> Phi </preform>
         <id> .K => N </id>
       </rule>
       (. =>
       <task>
         <ruleId> N </ruleId>
         <config>
           <k> K </k>
           Cfg
         </config>
         <formula> Phi </formula>
       </task>
       )
       when fresh(N:Int)

  rule <task
endmodule
