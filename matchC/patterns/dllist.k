kmod DLLIST-HP is
  including MATCHC-SEMANTICS + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE

  kvar N : Nat
  kvar ELEFT LEFT RIGHT ERIGHT ELEFT' LEFT' RIGHT' ERIGHT' P' : Int++
  kvar I I0 I1 I2 I3 I4 : Int++
  kvar Alpha Beta : Seq++
  kvar H : Map
  kvar K : K
  kvar Phi : Formula
  kvar CfgItems TaskItems : Bag


*** Definition of Lists***
  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> dllseg(ELEFT,LEFT)(RIGHT,ERIGHT,Alpha) H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi </form>
      TaskItems
    </task>
  =>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> H </heap> 
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi /\ (ELEFT === LEFT) /\ (RIGHT === ERIGHT) /\ (Alpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config >
        <k> K </k>
        <heap>
          (LEFT) |-> FreeInt(N) : (id("dllistNode").id("val"))
          (LEFT +Int 1) |-> FreeInt(N +Int 1) : (id("dllistNode").id("next"))
          (LEFT +Int 2) |-> FreeInt(N +Int 2) : (id("dllistNode").id("prev"))
          dllseg(LEFT, FreeInt(N +Int 1))(RIGHT, ERIGHT, FreeSeq(N +Int 3))
          H
        </heap>
        <counter> N +Int 4 </counter>
        CfgItems
      </config>
  <form>
    Phi /\ ~(LEFT === 0) /\ (Alpha === [FreeInt(N)] @ FreeSeq(N +Int 3))
  </form>
  TaskItems
 </task>
  if VALID(Phi ===> (P' === LEFT) \/ (P' === LEFT +Int 1) \/ (P' === LEFT +Int 2))
  [structural]

    rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> dllseg(ELEFT,LEFT)(RIGHT,ERIGHT,Alpha) H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi </form>
      TaskItems
    </task>
  =>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> H </heap> 
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi /\ (ELEFT === LEFT) /\ (ERIGHT === LEFT) /\ (Alpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config >
        <k> K </k>
        <heap>
	      (RIGHT) |-> FreeInt(N) : (id("dllistNode").id("val"))
          (RIGHT +Int 1) |-> FreeInt(N +Int 1) : (id("dllistNode").id("next"))
          (RIGHT +Int 2) |-> FreeInt(N +Int 2) : (id("dllistNode").id("prev"))
          dllseg(ELEFT, LEFT)(FreeInt(N +Int 2), RIGHT, FreeSeq(N +Int 3))
          H
        </heap>
	    <counter> N +Int 4 </counter>
        CfgItems
	  </config>
      <form>
        Phi /\ ~(RIGHT === 0) /\ (Alpha === FreeSeq(N +Int 3) @ [FreeInt(N)])
      </form>
      TaskItems
  </task>
  if VALID(Phi ===> (P' === RIGHT) \/ (P' === RIGHT +Int 1) \/ (P' === RIGHT +Int 2))
  [structural]

  rule
    <heap_> dllseg(ELEFT,0)(0,ERIGHT,Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ (ELEFT === 0) /\ (ERIGHT === 0) /\ Alpha === epsilon </form>
  [structural]

  rule
    <heap_> dllseg(LEFT,LEFT)(RIGHT,ERIGHT,Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ (RIGHT === ERIGHT) /\ Alpha === epsilon </form>
  [structural]
  
  rule
    <heap_> dllseg(ELEFT,LEFT)(RIGHT,RIGHT,Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ (ELEFT === LEFT) /\ Alpha === epsilon </form>
  [structural]

  rule
    <heap_> dllseg(ELEFT,LEFT)(RIGHT,ERIGHT,epsilon) => .Map <_/heap>
    <form> Phi => Phi /\ (LEFT === 0) /\ (RIGHT === 0) </form>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
      (LEFT) |-> I0 : (id("dllistNode").id("val"))
      (LEFT +Int 1) |-> I1 : (id("dllistNode").id("next"))
      (LEFT +Int 2) |-> I2 : (id("dllistNode").id("prev"))
      => dllseg(I2, LEFT)(LEFT, I1, [I0])
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        dllseg(ELEFT,LEFT)(RIGHT,ERIGHT,Alpha)
        dllseg(RIGHT,ERIGHT)(RIGHT',ERIGHT',Beta)
      =>     
        dllseg(ELEFT,LEFT)(RIGHT',ERIGHT', Alpha @ Beta)
    <_/heap>
     
  rule
    <heap_>
        dllist(LEFT,RIGHT)(Alpha)
      =>
        dllseg(0,LEFT)(RIGHT,0,Alpha)
    <_/heap>
  [structural]

  rule
    <heap_>
        dllseg(0,LEFT)(RIGHT,0,Alpha)
      =>
        dllist(LEFT,RIGHT)(Alpha)
    <_/heap>
  [structural]
  

  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <heap> dllist(LEFT)(Alpha) H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      TaskItems
    </task>
  =>
	<task>
    <taskType> Run </taskType>
    <config>
      <heap> dllist(LEFT,FreeInt(N))(Alpha) H </heap> 
      <counter> N +Int 1 </counter>
      CfgItems
    </config>
    TaskItems
  </task>
  [structural]
endkm
