require "matching-logic.k"

module NAIVE-DOMAIN-REASONING
  imports MATCHING-LOGIC

  syntax Bool ::= Map "impliesMap" Map [function]
                | K "impliesK" K [function]
                | List{K} "impliesList{K}" List{K} [function]
/*
  rule (< X:CellLabel > K:K </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > K2:K </ X:CellLabel > RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS
  rule (< X:CellLabel > B:Bag </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > B2:Bag </ X:CellLabel > RHS:Bag) => B impliesBag B2 andBool LHS impliesBag RHS
  rule (< X:CellLabel > M:Map </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > M2:Map </ X:CellLabel > RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS*/

  //TODO: remove
  rule (<T> B:Bag </T> LHS:Bag) impliesBag (<T> B2:Bag </T> RHS:Bag) => B impliesBag B2 andBool LHS impliesBag RHS
  rule (<k> K:K </k> LHS:Bag) impliesBag (<k> K2:K </k> RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS
  rule (<wcet> K:K </wcet> LHS:Bag) impliesBag (<wcet> K2:K </wcet> RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS
  rule (<pgm> M:Map </pgm> LHS:Bag) impliesBag (<pgm> M2:Map </pgm> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<mem> M:Map </mem> LHS:Bag) impliesBag (<mem> M2:Map </mem> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<reg> M:Map </reg> LHS:Bag) impliesBag (<reg> M2:Map </reg> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<timing> M:Map </timing> LHS:Bag) impliesBag (<timing> M2:Map </timing> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<input> M:Map </input> LHS:Bag) impliesBag (<input> M2:Map </input> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<status> M:Map </status> LHS:Bag) impliesBag (<status> M2:Map </status> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS

  rule .Bag impliesBag .Bag => true

  rule (Key |-> V1 LHS:Map) impliesMap (Key |-> V2 RHS:Map) => V1 impliesK V2 andBool LHS impliesMap RHS
  rule .Map impliesMap .Map => true

  rule I:Int impliesK I2:Int => I ==Int I2
  rule B:Bool impliesK B2:Bool => B ==Bool B2
  rule Lbl:KLabel ( Kl:List{K} ) impliesK Lbl ( Kl2:List{K} ) => Kl impliesList{K} Kl2 when isInt(Lbl(Kl)) =/=K true andBool isBool(Lbl(Kl)) =/=K true
  rule Lbl:KLabel ( _ ) impliesK Lbl2:KLabel ( _ ) => false when Lbl =/=KLabel Lbl2
  rule .K impliesK K => K ==K .K
  rule K impliesK .K => K ==K .K
  rule (L1:KLabel(Kl1:List{K}) ~> K2:K) impliesK (L1':KLabel(Kl1':List{K}) ~> K2') => L1(Kl1) impliesK L1'(Kl1') andBool K2 impliesK K2' when K2 =/=K .K andBool K2' =/=K .K

  rule K ,, Kl:List{K} impliesList{K} K2 ,, Kl2:List{K} => K impliesK K2 andBool Kl impliesList{K} Kl2
  rule .List{K} impliesList{K} .List{K} => true

  rule (<T>... <k> K </k> ...</T>) assertsBag (<T>... <k> K2 </k> ...</T>) => K impliesK K2

endmodule
