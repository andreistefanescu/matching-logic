kmod QUEUE-HP is
  including MATCHC-SEMANTICS + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE + LIST-HP

  kvar N : Nat
  kvar P P' Q Q' : Int++
  kvar I I1 I2 I3 I4 : Int++
  kvar Alpha Beta : Seq++
  kvar H : Map
  kvar K : K
  kvar Phi : Formula
  kvar CfgItems TaskItems : Bag


*** Definition of Queues ***
  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> queue(P)(Alpha) H </heap>
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
      <form> Phi /\ (P === 0) /\ (Alpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> K </k>
        <heap>
          P |-> FreeInt(N) : (id("queue").id("head"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("queue").id("tail"))
          queue(FreeInt(N), FreeInt(N +Int 1))(Alpha)
          H
        </heap>
        <counter> N +Int 2 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === 0)
      </form>
      TaskItems
    </task>
  if VALID(Phi ===> P' === P \/ P' === P +Int 1)
  [structural]

rule
  <task>
    <taskType> Run </taskType>
    <config>
      <k> derive(P') ~> K </k>
      <heap> queue(P, Q)(Alpha) H </heap>
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
    <form> Phi /\ (P === 0) /\ (Q === 0) /\ (Alpha === epsilon) </form>
    TaskItems
  </task>
  <task>
    <taskType> Run </taskType>
    <config>
      <k> K </k>
      <heap>
        lseg(P, Q)(FreeSeq(N))
        Q |-> FreeInt(N +Int 1) : (id("listNode").id("val"))
        (Q +Int 1) |-> FreeInt(N +Int 2) : (id("listNode").id("next"))
        H
      </heap>
      <counter> N +Int 3 </counter>
      CfgItems
    </config>
    <form>
      Phi /\ ~(P === 0) /\ ~(Q === 0) /\ (Alpha === FreeSeq(N) @ [FreeInt(N +Int 1)])
    </form>
    TaskItems
  </task>
if VALID(Phi ===> P' === P \/ P' === P +Int 1 \/ P' === Q \/ P' === Q +Int 1)
[structural]

  rule
    <taskType> Run </taskType>
    <heap>
        queue(P)(Alpha)
      =>
        P |-> FreeInt(N) : (id("queue").id("head"))
        (P +Int 1) |-> FreeInt(N +Int 1) : (id("queue").id("tail"))
        queue(FreeInt(N), FreeInt(N +Int 1))(Alpha)
    <_/heap>
    <counter> N => N +Int 2 </counter>
    <form>
      Phi /\ ~(P === 0) => Phi /\ ~(P === 0) 
    </form>
  [structural]

  rule
    <heap_> queue(0)(Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ Alpha === epsilon </form>
  [structural]

  rule
    <heap_> queue(P)(epsilon) => .Map <_/heap>
    <form> Phi => Phi /\ P === 0 </form>

  rule
  <taskType> Hypothesis </taskType>
    <heap_>
      P |-> I : (id("queue").id("head"))
      (P +Int 1) |-> 0 : (id("queue").id("tail"))
      =>
      queue(P)(epsilon)
    <_/heap>

  rule
  <taskType> Hypothesis </taskType>
    <heap_>
      P |-> 0 : (id("queue").id("head"))
      (P +Int 1) |-> I : (id("queue").id("tail"))
      =>
      queue(P)(epsilon)
    <_/heap>

  rule
    <heap_>
      P |-> I1 : (id("queue").id("head"))
      (P +Int 1) |-> I2 : (id("queue").id("tail"))
      lseg(I1, I2)(Alpha)
      I2 |-> I3 : (id("listNode").id("val"))
      (I2 +Int 1) |-> I4 : (id("listNode").id("next"))
      =>
      queue(P)(Alpha @ [I3])
    <_/heap>
  [structural]



  rule
    <heap_>
      queue(P, 0)(Alpha) => .Map
    <_/heap>
    <form> Phi => Phi /\ P === 0 /\ Alpha === epsilon </form>
  [structural]

  rule
    <heap_>
      queue(0, Q)(Alpha) => .Map
    <_/heap>
    <form> Phi => Phi /\ Q === 0 /\ Alpha === epsilon </form>
  [structural]


  rule
    <heap_>
      lseg(P, P')(Alpha)
      queue(P', Q)(Beta)
      =>
      queue(P, Q)(Alpha @ Beta)
    <_/heap>
  [structural]

endkm
