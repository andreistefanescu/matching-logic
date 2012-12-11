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
           </rhs>
         ...</rhss>
       </task>
       => .Bag 
       when checkSat(notBool(Phi impliesBool (Phi' andBool LHS impliesBag RHS))) ==String "unsat" [structural]

  rule [dissolve-fails]: (<task>
         <lhs>...
           <config> LHS:Bag </config>
           <formula> Phi:Bool </formula>
         ...</lhs>
         <rhss>...
           <rhs>
             <rconfig> RHS:Bag </rconfig>
             <rformula> Phi':Bool </rformula>
           </rhs>
         ...</rhss>
       </task>)
       => stuck 
       when checkSat(notBool(Phi impliesBool (Phi' andBool LHS impliesBag RHS))) =/=String "unsat"
       andBool checkSat(notBool(Phi impliesBool (LHS assertsBag RHS))) ==String "unsat" [structural]


  syntax Bool ::= Bag "impliesBag" Bag [function]
  syntax Bool ::= Bag "assertsBag" Bag [function]

  syntax Map ::= "#symMap" "(" Int ")" [klabel('#symMap)]
  rule isSymbolicK(Map2KLabel _:Map #symMap(_)(.List{K})) => true

  rule <task>...
         <lhs>...
           <formula> Phi:Bool </formula>
         ...</lhs>
       </task>
       => .Bag
       when checkSat(Phi) ==String "unsat" [structural]

  syntax BagItem ::= "stuck"
  rule stuck stuck => stuck

  syntax Bool ::= K "inSymbolic" Set [function]
  rule [inSymbolic-int]: I:Int inSymbolic SetItem(I2:Int) S:Set => I ==Int I2 orBool I inSymbolic S [structural]
  rule I:Int inSymbolic SetItem(K) S:Set => I inSymbolic S when isInt(K) =/=K true [structural]
  rule B:Bool inSymbolic SetItem(B2:Bool) S:Set => B ==Bool B2 orBool B inSymbolic S [structural]
  rule B:Bool inSymbolic SetItem(K) S:Set => B inSymbolic S when isBool(K) =/=K true [structural]
  rule _ inSymbolic .Set => false [structural]
  rule K inSymbolic S:Set => K in S when isInt(K) =/=K true andBool isBool(K) =/=K true [structural]
endmodule
