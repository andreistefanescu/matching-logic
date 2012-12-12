require "lib/naive-domain-reasoning.k"
require "wcet.k"

module WCET-DOMAIN-REASONING
  imports NAIVE-DOMAIN-REASONING
  imports WCET

/*
  rule manual => SetItem(status)
*/

  rule (<status> M:Map </status> LHS:Bag) impliesBag (<status> M2:Map </status> RHS:Bag) => arrayTransform(M) impliesMap M2 andBool LHS impliesBag RHS

  syntax Map ::= arrayTransform(Map)

  rule arrayTransform(M:Map[.Map(_:K)]) => M [structural]
  rule arrayTransform((X:Id |-> I M:Map)[(I2:Int |-> Map2KLabel (X:Id |-> I3:Int) M2:Map(.List{K}) M3:Map)(I4:Int)] => (X |-> #if I4 ==Int I2 #then I3 #else I #fi M)[(I2 |-> Map2KLabel M2(.List{K}) M3)(I4)]) [structural]
  rule arrayTransform(M:Map[((_ |-> Map2KLabel .(.List{K}) => .) _)(_:K)]) [structural]
  rule arrayTransform(K |-> K2 M:Map) => K |-> K2 arrayTransform(M)
  rule arrayTransform(.Map) => .Map

  rule (I +Int I2:#Int) +Int I3:#Int => I +Int (I2 +Int I3) when isSymbolicInt(I)

endmodule
