require "matching-logic.k"

module NAIVE-DOMAIN-REASONING
  imports MATCHING-LOGIC

  syntax Bool ::= Map "impliesMap" Map [function]
                | K "impliesK" K [function]
                | List "impliesList" List [function]
                | KList "impliesKList" KList [function]
                | Set "impliesSet" Set [function]

  syntax Set ::= manual(KLabel)
/*
  rule (< X:CellLabel > K:K </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > K2:K </ X:CellLabel > RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS when notBool(X in manual('_impliesBag_))
  rule (< X:CellLabel > B:Bag </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > B2:Bag </ X:CellLabel > RHS:Bag) => B impliesBag B2 andBool LHS impliesBag RHS when notBool(X in manual('_impliesBag_))
  rule (< X:CellLabel > M:Map </ X:CellLabel > LHS:Bag) impliesBag (< X:CellLabel > M2:Map </ X:CellLabel > RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS when notBool(X in manual('_impliesBag)) */

  //TODO: remove
  rule (<T> B:Bag </T> LHS:Bag) impliesBag (<T> B2:Bag </T> RHS:Bag) => B impliesBag B2 andBool LHS impliesBag RHS
  rule (<k> K:K </k> LHS:Bag) impliesBag (<k> K2:K </k> RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS
  rule (<wcet> K:K </wcet> LHS:Bag) impliesBag (<wcet> K2:K </wcet> RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS
  rule (<pgm> M:Map </pgm> LHS:Bag) impliesBag (<pgm> M2:Map </pgm> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<mem> M:Map </mem> LHS:Bag) impliesBag (<mem> M2:Map </mem> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<reg> M:Map </reg> LHS:Bag) impliesBag (<reg> M2:Map </reg> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<timing> M:Map </timing> LHS:Bag) impliesBag (<timing> M2:Map </timing> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<input> L:List </input> LHS:Bag) impliesBag (<input> L2:List </input> RHS:Bag) => L impliesList L2 andBool LHS impliesBag RHS
  rule (<status> M:Map </status> LHS:Bag) impliesBag (<status> M2:Map </status> RHS:Bag) => M impliesMap M2 andBool LHS impliesBag RHS
  rule (<timers> L:List </timers> LHS:Bag) impliesBag (<timers> L2:List </timers> RHS:Bag) => L impliesList L2 andBool LHS impliesBag RHS
  rule (<priority> K:K </priority> LHS:Bag) impliesBag (<priority> K2:K </priority> RHS:Bag) => K impliesK K2 andBool LHS impliesBag RHS
  rule (<stack> L:List </stack> LHS:Bag) impliesBag (<stack> L2:List </stack> RHS:Bag) => L impliesList L2 andBool LHS impliesBag RHS
  rule (<interrupts> S:Set </interrupts> LHS:Bag) impliesBag (<interrupts> S2:Set </interrupts> RHS:Bag) => S impliesSet S2 andBool LHS impliesBag RHS

  rule .Bag impliesBag .Bag => true

  rule (Key |-> V1 LHS:Map) impliesMap (Key |-> V2 RHS:Map) => V1 impliesK V2 andBool LHS impliesMap RHS
  rule .Map impliesMap M => M ==Map .Map
  rule M impliesMap .Map => M ==Map .Map

  rule (ListItem(K) LHS:List) impliesList (ListItem(K2) RHS:List) => K impliesK K2 andBool LHS impliesList RHS
  rule L:List impliesList .List => L ==List .List
  rule .List impliesList L:List => L ==List .List

  rule I:Int impliesK I2:Int => I ==Int I2
  rule B:Bool impliesK B2:Bool => B ==Bool B2
  rule Lbl:KLabel ( Kl:KList ) impliesK Lbl ( Kl2:KList ) => Kl impliesKList Kl2 when isInt(Lbl(Kl)) =/=K true andBool isBool(Lbl(Kl)) =/=K true
  rule Lbl:KLabel ( _ ) impliesK Lbl2:KLabel ( _ ) => false when Lbl =/=KLabel Lbl2
  rule .K impliesK K => K ==K .K
  rule K impliesK .K => K ==K .K
  rule (L1:KLabel(Kl1:KList) ~> K2:K) impliesK (L1':KLabel(Kl1':KList) ~> K2') => L1(Kl1) impliesK L1'(Kl1') andBool K2 impliesK K2' when K2 =/=K .K orBool K2' =/=K .K

  rule K ,, Kl:KList impliesKList K2 ,, Kl2:KList => K impliesK K2 andBool Kl impliesKList Kl2
  rule .KList impliesKList .KList => true

  rule SI:SetItem S:Set impliesSet SI:SetItem S2:Set => S impliesSet S2
  rule .Set impliesSet S:Set => S ==Set .Set
  rule S:Set impliesSet .Set => S ==Set .Set

/*
  rule (< X:CellLabel > K:K </ X:CellLabel > LHS:Bag) assertsBag (< X:CellLabel > K2:K </ X:CellLabel > RHS:Bag) => LHS assertsBag RHS when notBool(X in manual('_assertsBag_))
  rule (< X:CellLabel > B:Bag </ X:CellLabel > LHS:Bag) assertsBag (< X:CellLabel > B2:Bag </ X:CellLabel > RHS:Bag) => B assertsBag B2 andBool LHS assertsBag RHS when notBool(X in manual('_assertsBag_))
  rule (< X:CellLabel > M:Map </ X:CellLabel > LHS:Bag) assertsBag (< X:CellLabel > M2:Map </ X:CellLabel > RHS:Bag) => LHS assertsBag RHS when notBool(X in manual('_assertsBag_)) */

  rule .Bag assertsBag .Bag => true

endmodule
