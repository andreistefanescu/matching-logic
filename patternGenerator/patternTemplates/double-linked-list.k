kmod DLIST-HP is
  including MATCHC-SEMANTICS + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE

  kvar N : Nat
  kvar P P' P1 P2 Q Q' Q1 Q2 : Int++
  kvar I : Int++
  kvar Alpha Beta : Seq++
  kvar H : Map
  kvar K : K
  kvar Phi : Formula
  kvar NtPhi : NtFormula
  kvar CfgItems TaskItems : Bag


*** Definition of Lists ***
  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> dlseg(P,Q)(P1,Q1,Alpha) H </heap>
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
      <form> Phi /\ (P === P1) /\ (Q === Q1) /\ (Alpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config >
        <k> K </k>
        <heap>
          P |-> FreeInt(N) : (id("dlistNode").id("val"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("dlistNode").id("next"))
          (P +Int 2) |-> Q1 : (id("dlistNode").id("prev"))
          dlseg(FreeInt(N +Int 1),Q)(P1,P,FreeSeq(N +Int 2))
          H
        </heap>
        <counter> N +Int 3 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === P1) /\ ~(Q === Q1) /\ (Alpha === [FreeInt(N)] @ FreeSeq(N +Int 2))
      </form>
      TaskItems
    </task>
  if VALID(Phi ===> P' === P \/ P' === P +Int 1 \/ P' === P +Int 2)
  [structural]

    rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(Q') ~> K </k>
        <heap> dlseg(P,Q)(P1,Q1,Alpha) H </heap>
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
        <k> derive(Q') ~> K </k>
        <heap> H </heap> 
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi /\ (P === P1) /\ (Q === Q1) /\ (Alpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config >
        <k> K </k>
        <heap>
          Q |-> FreeInt(N) : (id("dlistNode").id("val"))
          (Q +Int 1) |-> P1 : (id("dlistNode").id("next"))
          (Q +Int 2) |-> FreeInt(N +Int 1) : (id("dlistNode").id("prev"))
          dlseg(P,FreeInt(N +Int 1))(Q,Q1,FreeSeq(N +Int 2))
          H
        </heap>
        <counter> N +Int 3 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === P1) /\ ~(Q === Q1) /\ (Alpha === FreeSeq(N +Int 2) @ [FreeInt(N)])
      </form>
      TaskItems
    </task>
  if VALID(Phi ===> Q' === Q \/ Q' === Q +Int 1 \/ Q' === Q +Int 2)
  [structural]

  rule
    <heap_> dlseg(0,0)(P,Q,Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ (P === 0) /\ (Q === 0) /\ Alpha === epsilon </form>
  [structural]
    rule
    <heap_> dlseg(P,Q)(P,Q1,Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ (Q === Q1) /\ Alpha === epsilon </form>
  [structural]
  rule
    <heap_> dlseg(P,Q)(P1,Q,Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ (P === P1) /\ Alpha === epsilon </form>
  [structural]

  rule
    <heap_> dlseg(P,Q)(P1,Q1,epsilon) => .Map <_/heap>
    <form> Phi => Phi /\ (P === 0) /\ (Q === 0) </form>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("dlistNode").id("val"))
        (P +Int 1) |-> Q1 : (id("dlistNode").id("next"))
        (P +Int 2) |-> Q2 : (id("dlistNode").id("prev"))
      => 
        dlseg(P,P)(Q1,Q2,[I])
    <_/heap>
  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        dlseg(P,Q')(P',P1,Alpha)
        dlseg(P',Q)(Q1,Q',Beta)
      =>     
        dlseg(P,Q)(Q1,P1, Alpha @ Beta)
    <_/heap>
     
  rule
    <heap_>
        dlinkedlist(P,Q)(Alpha)
      =>
        dlseg(P,Q)(0,0,Alpha)
    <_/heap>
  [structural]
  

  rule
        <heap> dlist(P')(Alpha) H </heap>
  =>
        <heap> dlinkedlist(P',P')(Alpha) H </heap> 
  [structural]
endkm
