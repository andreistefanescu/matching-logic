module MATCHING-LOGIC
/*
  configuration
    <top>
      <tasks>
        <task multiplicity="*">
          <lhs>
            <config>
              <T extern="true" />
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
*/

  rule [dissolve]: <task>
         <lhs>...
           <config> LHS:Bag </config>
           <formula> Phi:Bool </formula>
         ...</lhs>
         <rhss>...
           <rhs>
             <rconfig> RHS:Bag </rconfig>
             <rformula> Phi':Bool </rformula>
             <rfreevars> S:Set </rfreevars>
           </rhs>
         ...</rhss>
       </task>
       => assertValid(exists S . (Phi impliesBool (Phi' andBool LHS impliesBag RHS)))
       when isValid(exists S . (Phi impliesBool ((LHS assertsBag RHS)))) [structural]

  syntax Bool ::= Bag "impliesBag" Bag [function]
  syntax Bool ::= Bag "assertsBag" Bag [function]

  rule [infeasible]:
       <task>...
         <lhs>...
           <formula> Phi:Bool </formula>
         ...</lhs>
       </task>
       => .Bag
       when isValid(notBool Phi) [structural]

  syntax BagItem ::= stuck(Bool)
  syntax BagItem ::= stuck(Bool, String)

  syntax Bool ::= K "inSymbolic" Set [function]
  rule [inSymbolic-int]: I:Int inSymbolic SetItem(I2:Int) S:Set => I ==Int I2 orBool I inSymbolic S [structural]
  rule I:Int inSymbolic SetItem(K) S:Set => I inSymbolic S when isInt(K) =/=K true [structural]
  rule B:Bool inSymbolic SetItem(B2:Bool) S:Set => B ==Bool B2 orBool B inSymbolic S [structural]
  rule B:Bool inSymbolic SetItem(K) S:Set => B inSymbolic S when isBool(K) =/=K true [structural]
  rule _ inSymbolic .Set => false [structural]
  rule K inSymbolic S:Set => K in S when isInt(K) =/=K true andBool isBool(K) =/=K true [structural]

  syntax Bool ::= isValid(Bool) [function]
  rule [isValid]: isValid(T:Bool) => checkSat(notBool(T)) ==String "unsat"

  syntax BagItem ::= assertValid(Bool) [function]
  rule assertValid(T) => .Bag when isValid(T)
  rule assertValid(T) => stuck(T) when notBool(isValid(T))

  rule stuck(T) => stuck(T, SMTLibQuery(T))
endmodule
