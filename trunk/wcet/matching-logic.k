module MATCHING-LOGIC
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

  rule (< X:CellLabel > K:K </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > K2:K </ X:CellLabel > RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS
  rule (< X:CellLabel > B:Bag </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > B2:Bag </ X:CellLabel > RHS:Bag) => B impliesBag B2 andBool LHS impliesBag RHS
  rule (< X:CellLabel > M:Map </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > M2:Map </ X:CellLabel > RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS

  rule .Bag impliesBag .Bag => true

  rule (Key |-> V1 LHS:Map) impliesMap (Key |-> V2 RHS:Map) => V1 impliesK V2 andBool LHS impliesMap RHS

  rule .Map impliesMap .Map => true


