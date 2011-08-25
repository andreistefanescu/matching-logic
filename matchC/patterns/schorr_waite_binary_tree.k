kmod SCHORR-WAITE-BINARY-TREE-HP is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE
          + MATHEMATICAL-TREE-BUILTIN-MODULE

  kvar N : Nat
  kvar P P' Q Q1 Q2 : Int++
  kvar I : Int++
  kvar Sigma Tau : Tree++
  kvar H : Map
  kvar K : K
  kvar Phi : Formula
  kvar CfgItems TaskItems : Bag


*** Definition of SW Trees ***
  rule
  (
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> swtree(P)(Tau) H </heap>
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
      <form> Phi /\ (P === 0) /\ (Tau === upsilon) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> K </k>
        <heap>
          P |-> FreeInt(N) : (id("graphNode").id("mark"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("graphNode").id("left"))
          (P +Int 2) |-> FreeInt(N +Int 2) : (id("graphNode").id("right"))
          swtree(FreeInt(N +Int 1))(FreeTree(N +Int 3))
          swtree(FreeInt(N +Int 2))(FreeTree(N +Int 4))
          H
        </heap>
        <counter> N +Int 5 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === 0)
        /\ Tau === (FreeTree(N +Int 3) [[P] @ [FreeInt(N)]] FreeTree(N +Int 4))
      </form>
      TaskItems
    </task>
  )
  if VALID(Phi ===> P' === P \/ P' === P +Int 1 \/ P' === P +Int 2)
  [structural]


  rule
    <heap_> swtree(0)(Tau) => .Map <_/heap>
    <form> Phi => Phi /\ Tau === upsilon </form>
  [structural]
  rule
    <heap_> swtree(P)(upsilon) => .Map <_/heap>
    <form> Phi => Phi /\ P === 0 <_/form>
  [structural]

  rule
    <taskType> Run </taskType>
    <heap_>
        swtree(P)(Tau)
      =>
        P |-> FreeInt(N) : (id("graphNode").id("mark"))
        (P +Int 1) |-> FreeInt(N +Int 1) : (id("graphNode").id("left"))
        (P +Int 2) |-> FreeInt(N +Int 2) : (id("graphNode").id("right"))
        swtree(FreeInt(N +Int 1))(FreeTree(N +Int 3))
        swtree(FreeInt(N +Int 2))(FreeTree(N +Int 4))
    <_/heap>
    <counter> N => N +Int 5 </counter>
    <form>
        Phi /\ ~(P === 0)
      =>
        Phi /\ ~(P === 0)
        /\ Tau === (FreeTree(N +Int 3) [[P] @ [FreeInt(N)]] FreeTree(N +Int 4))
    </form>
  [structural]
  rule
    <taskType> Run </taskType>
    <heap_>
        swtree(P)(Tau)
      =>
        P |-> FreeInt(N) : (id("graphNode").id("mark"))
        (P +Int 1) |-> FreeInt(N +Int 1) : (id("graphNode").id("left"))
        (P +Int 2) |-> FreeInt(N +Int 2) : (id("graphNode").id("right"))
        swtree(FreeInt(N +Int 1))(FreeTree(N +Int 3))
        swtree(FreeInt(N +Int 2))(FreeTree(N +Int 4))
    <_/heap>
    <counter> N => N +Int 5 </counter>
    <form>
        Phi /\ ~(Tau === upsilon)
      =>
        Phi /\ ~(P === 0)
        /\ Tau === (FreeTree(N +Int 3) [[P] @ [FreeInt(N)]] FreeTree(N +Int 4))
    </form>
  [structural]


  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("graphNode").id("mark"))
        (P +Int 1) |-> 0 : (id("graphNode").id("left"))
        (P +Int 2) |-> 0 : (id("graphNode").id("right"))
      =>
        swtree(P)(upsilon [[P] @ [I]] upsilon)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("graphNode").id("mark"))
        (P +Int 1) |-> Q : (id("graphNode").id("left"))
        (P +Int 2) |-> 0 : (id("graphNode").id("right"))
        swtree(Q)(Tau)
      =>
        swtree(P)(Tau [[P] @ [I]] upsilon)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("graphNode").id("mark"))
        (P +Int 1) |-> 0 : (id("graphNode").id("left"))
        (P +Int 2) |-> Q : (id("graphNode").id("right"))
        swtree(Q)(Tau)
      =>
        swtree(P)(upsilon [[P] @ [I]] Tau)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("graphNode").id("mark"))
        (P +Int 1) |-> Q1 : (id("graphNode").id("left"))
        (P +Int 2) |-> Q2 : (id("graphNode").id("right"))
        swtree(Q1)(Tau)
        swtree(Q2)(Sigma)
      =>
        swtree(P)(Tau [[P] @ [I]] Sigma)
    <_/heap>
endkm 

