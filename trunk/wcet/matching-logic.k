require "builtins/smt.k"

module MATCHING-LOGIC
  imports SMT-HOOKS
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
       when checkSat(notBool(Phi impliesBool (Phi' andBool LHS impliesBag RHS))) ==K unsat [structural]

  syntax Bool ::= Bag "impliesBag" Bag [function]

  syntax Map ::= "#symMap" "(" Int ")" [klabel('#symMap)]
  rule isSymbolicK(Map2KLabel _:Map #symMap(_)(.List{K})) => true

  rule <task>...
         <lhs>...
           <formula> Phi:Bool </formula>
         ...</lhs>
       </task>
       => .Bag
       when checkSat(Phi) ==K unsat [structural]

endmodule
