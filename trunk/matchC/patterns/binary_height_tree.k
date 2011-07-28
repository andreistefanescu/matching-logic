kmod BINARY-HEIGHT-TREE-HP is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE
          + MATHEMATICAL-TREE-BUILTIN-MODULE

  kvar N : Nat
  kvar P P' Q Q1 Q2 : Int++
  kvar I J : Int++
  kvar Sigma Tau : Tree++
  kvar H : Map
  kvar K : K
  kvar Phi : Formula
  kvar CfgItems TaskItems : Bag

*** Definition of Trees ***
  rule
  (
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P') ~> K </k>
        <heap> htree(P)(Tau) H </heap>
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
          P |-> FreeInt(N) : (id("node").id("value"))
          (P +Int 1) |-> FreeInt(N +Int 1) : (id("node").id("height"))
          (P +Int 2) |-> FreeInt(N +Int 2) : (id("node").id("left"))
          (P +Int 3) |-> FreeInt(N +Int 3) : (id("node").id("right"))
          htree(FreeInt(N +Int 2))(FreeTree(N +Int 4))
          htree(FreeInt(N +Int 3))(FreeTree(N +Int 5))
          H
        </heap>
        <counter> N +Int 6 </counter>
        CfgItems
      </config>
      <form>
        Phi /\ ~(P === 0)
        /\ (Tau === (FreeTree(N +Int 4)
                    [[FreeInt(N)] @ [FreeInt(N +Int 1)]]
                    FreeTree(N +Int 5)))
      </form>
      TaskItems
    </task>
  )
  if VALID(Phi ===> P' === P \/ P' === P +Int 1
                    \/ P' === P +Int 2 \/ P' === P +Int 3)
  [structural]

  rule
    <heap_> htree(0)(Tau) => .Map <_/heap>
    <form> Phi => Phi /\ Tau === upsilon </form>
  [structural]
  rule
    <heap_> htree(P)(upsilon) => .Map <_/heap>
    <form> Phi => Phi /\ P === 0 <_/form>
  [structural]

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("node").id("value"))
        (P +Int 1) |-> J : (id("node").id("height"))
        (P +Int 2) |-> 0 : (id("node").id("left"))
        (P +Int 3) |-> 0 : (id("node").id("right"))
      =>
        htree(P)(upsilon [[I] @ [J]] upsilon)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("node").id("value"))
        (P +Int 1) |-> J : (id("node").id("height"))
        (P +Int 2) |-> Q : (id("node").id("left"))
        (P +Int 3) |-> 0 : (id("node").id("right"))
        htree(Q)(Tau)
      =>
        htree(P)(Tau [[I] @ [J]] upsilon)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("node").id("value"))
        (P +Int 1) |-> J : (id("node").id("height"))
        (P +Int 2) |-> 0 : (id("node").id("left"))
        (P +Int 3) |-> Q : (id("node").id("right"))
        htree(Q)(Tau)
      =>
        htree(P)(upsilon [[I] @ [J]] Tau)
    <_/heap>

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("node").id("value"))
        (P +Int 1) |-> J : (id("node").id("height"))
        (P +Int 2) |-> Q1 : (id("node").id("left"))
        (P +Int 3) |-> Q2 : (id("node").id("right"))
        htree(Q1)(Tau)
        htree(Q2)(Sigma)
      =>
        htree(P)(Tau [[I] @ [J]] Sigma)
    <_/heap>
endkm 

