require "builtins/symbolic-calculus.k"
require "builtins/smt.k"

module MATCHING-LOGIC
  imports SYMBOLIC-CALCULUS
  rule <task>
         <lhs>
           <config> LHS:Bag </config>
           <formula> Phi:Bool </formula>
         </lhs>
         <rhss>...
           <rhs>
             <config> RHS:Bag </config>
             <formula> Phi':Bool </formula>
           </rhs>
         ...</rhss>
       </task>
       => .Bag 
       when checkSat(notBool(Phi impliesBool (Phi' andBool LHS impliesBag RHS))) ==K unsat [structural]

  syntax Bool ::= Bag "impliesBag" Bag [function]
                | Map "impliesMap" Map [function]
                | K "impliesK" K [function]
                | List{K} "impliesList{K}" List{K} [function]

  rule (< X:CellLabel > K:K </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > K2:K </ X:CellLabel > RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS
  rule (< X:CellLabel > B:Bag </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > B2:Bag </ X:CellLabel > RHS:Bag) => B impliesBag B2 andBool LHS impliesBag RHS
  rule (< X:CellLabel > M:Map </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > M2:Map </ X:CellLabel > RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule .Bag impliesBag .Bag => true

  rule (Key |-> V1 LHS:Map) impliesMap (Key |-> V2 RHS:Map) => V1 impliesK V2 andBool LHS impliesMap RHS
  rule .Map impliesMap .Map => true

  rule I:Int impliesK I2:Int => I ==Int I2
  rule B:Bool impliesK B2:Bool => B ==Bool B2
  rule Lbl:KLabel ( Kl:List{K} ) impliesK Lbl ( Kl2:List{K} ) => Kl impliesList{K} Kl2
  rule Lbl:KLabel ( _ ) impliesK Lbl2:KLabel ( _ ) => false when Lbl =/=KLabel Lbl2
  rule .K impliesK .K => true

  rule K ,, Kl:List{K} impliesList{K} K2 ,, Kl2:List{K} => K impliesK K2 andBool Kl impliesList{K} Kl2
  rule .List{K} impliesList{K} .List{K} => true

  rule <task>...
         <lhs>...
           <formula> Phi:Bool </formula>
         ...</lhs>
       </task>
       => .Bag
       when checkSat(Phi) ==K unsat [structural]

endmodule
