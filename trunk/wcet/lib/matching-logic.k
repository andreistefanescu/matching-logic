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
             <rfreevars> SetItem(K) S:Set </rfreevars>
           </rhs>
         ...</rhss>
       </task>
       => assertValid(exists SetItem(K) S . (Phi impliesBool (Phi' andBool LHS impliesBag RHS)), LHS, Phi, RHS, Phi')
       when LHS assertsBag RHS [structural]

  rule [dissolve]: <task>
         <lhs>...
           <config> LHS:Bag </config>
           <formula> Phi:Bool </formula>
         ...</lhs>
         <rhss>...
           <rhs>
             <rconfig> RHS:Bag </rconfig>
             <rformula> Phi':Bool </rformula>
             <rfreevars> .Set </rfreevars>
           </rhs>
         ...</rhss>
       </task>
       => assertValid((Phi impliesBool (Phi' andBool LHS impliesBag RHS)), LHS, Phi, RHS, Phi')
       when LHS assertsBag RHS [structural]

  rule [infeasible]: <task>...
    <lhs>...
      <formula> Phi:Bool </formula>
    ...</lhs>
  ...</task> => .Bag when isValid(notBool Phi) [structural]


  syntax Bool ::= Bag "impliesBag" Bag [function]
  syntax Bool ::= Bag "assertsBag" Bag [function]

  syntax BagItem ::= stuck(Bool)
  syntax BagItem ::= stuck(Bool, String)
  syntax BagItem ::= stuck(Bag, Bool, Bag, Bool, String)

  syntax Bool ::= K "inSymbolic" Set [function]
  rule [inSymbolic-int]: I:Int inSymbolic SetItem(I2:Int) S:Set => I ==Int I2 orBool I inSymbolic S [structural]
  rule I:Int inSymbolic SetItem(K) S:Set => I inSymbolic S when isInt(K) =/=K true [structural]
  rule B:Bool inSymbolic SetItem(B2:Bool) S:Set => B ==Bool B2 orBool B inSymbolic S [structural]
  rule B:Bool inSymbolic SetItem(K) S:Set => B inSymbolic S when isBool(K) =/=K true [structural]
  rule _ inSymbolic .Set => false [structural]
  rule K inSymbolic S:Set => K in S when isInt(K) =/=K true andBool isBool(K) =/=K true [structural]

  syntax Bool ::= isValid(Bool) [function]
  rule [isValid]: isValid(T:Bool) => checkSat(notBool(T)) ==String "unsat"

  syntax BagItem ::= assertValid(Bool, Bag, Bool, Bag, Bool) [function]
  rule [assertValid]: assertValid(T, _, _, _, _) => .Bag when isValid(T)
  rule [assertValid]: assertValid(T, LHS, Phi, RHS, Phi') => stuck(LHS, Phi, RHS, Phi', SMTLibQuery(notBool(T))) when notBool(isValid(T))

  rule stuck(T) => stuck(T, SMTLibQuery(notBool(T)))
endmodule
