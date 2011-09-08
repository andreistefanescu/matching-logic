kmod DLLIST-HP is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE

  kvar N : Nat
  kvar P P' Q Q' : Int++
  kvar I : Int++
  kvar Alpha Beta : Seq++
  kvar H : Map
  kvar K : K
  kvar Phi : Formula
  kvar CfgItems TaskItems : Bag



  rule
  (
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> dllist(P)(Alpha) H </heap>
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
          P |-> FreeInt(N) : (id("dllistNode").id("val"))
          (P +Int 1) |-> 0 : (id("dllistNode").id("prev"))
          (P +Int 2) |-> FreeInt(N +Int 1) : (id("dllistNode").id("next"))
          dllist(FreeInt(N +Int 1))(FreeSeq(N +Int 2))
          H
        </heap>
        <counter> N +Int 4 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === 0)
        /\ (Alpha === ([FreeInt(N)] @ FreeSeq(N +Int 2)))
      </form>
      TaskItems
    </task>
  )
  if VALID(Phi ===> P' === P \/ P' === P +Int 1 \/ P' === P +Int 2)
  [structural]

  rule
    <heap_> dllist(0)(Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ Alpha === epsilon </form>
  [structural]
  rule
    <heap_> dllist(P)(epsilon) => .Map <_/heap>
    <form> Phi => Phi /\ P === 0 <_/form>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("dllistNode").id("val"))
        (P +Int 1) |-> 0 : (id("dllistNode").id("prev"))
        (P +Int 2) |-> 0 : (id("dllistNode").id("next"))
      =>
        dllist(P)([I])
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("dllistNode").id("val"))
        (P +Int 1) |-> 0 : (id("dllistNode").id("prev"))
        (P +Int 2) |-> Q : (id("dllistNode").id("next"))
        dllist(Q)(Alpha)
      =>
        dllist(P)([ I ] @ Alpha)
    <_/heap>





  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> dllseg(P, Q)(Alpha) H </heap>
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi </form>
      TaskItems
    </tasks>
  =>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> H </heap> 
        <counter> N </counter>
        CfgItems
      </config>
      <form> Phi /\ (P === Q) /\ (Alpha === epsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config >
        <k> K </k>
        <heap>
          P |-> FreeInt(N) : (id("dllistNode").id("val"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("dllistNode").id("prev"))
          (P +Int 2) |-> FreeInt(N +Int 2) : (id("dllistNode").id("next"))
          dllseg(FreeInt(N +Int 2), Q)(FreeSeq(N +Int 3))
          H
        </heap>
        <counter> N +Int 4 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === Q) /\ (Alpha === [FreeInt(N)] @ FreeSeq(N +Int 3))
      </form>
      TaskItems
    </task>
  if VALID(Phi ===> P' === P \/ P' === P +Int 1 \/ P' === P +Int 2)
  [structural]

  rule
    <heap_> dllseg(P, P)(Alpha) => .Map <_/heap>
    <form> Phi => Phi /\ Alpha === epsilon </form>
  [structural]
  rule
    <heap> dllseg(P, 0)(Alpha) => dllist(P)(Alpha) <_/heap>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("dllistNode").id("val"))
        (P +Int 1) |-> Q' : (id("dllistNode").id("prev"))
        (P +Int 2) |-> Q : (id("dllistNode").id("next"))
      =>
        dllseg(P, Q)([I])
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        dllseg(P, P')(Alpha)
        dllseg(P', Q)(Beta)
      =>
        dllseg(P, Q)(Alpha @ Beta)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        dllseg(P, P')(Alpha)
        dllist(P')(Beta)
      =>
        list(P)(Alpha @ Beta)
    <_/heap>

endkm 
