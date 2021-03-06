kmod SCHORR-WAITE-GRAPH-HP is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE
          + MATHEMATICAL-GRAPH-BUILTIN-MODULE

  kvar N : Nat
  kvar Phi : Formula
  kvar P P1 P2 Q Q1 Q2 : Int++
  kvar I : Int++
  kvar G G1 G2 : Graph
  kvar K : K
  kvar CfgItems TaskItems : Bag
  kvar H : Map


*** Definition of Points-to Graphs ***
  rule
  (
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P) ~> K </k>
        <heap> graph(P, B)(G) H </heap>
        CfgItems
      </config>
      <form> Phi </form>
      TaskItems
    </task>
  =>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> K </k>
        <heap> graph(P, B)(G) H </heap>
        CfgItems
      </config>
      <form> Phi /\ P === 0 /\ G === emptyGraph </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> K </k>
        <heap> graph(P, B)(G) H </heap>
        CfgItems
      </config>
      <form> Phi /\ ~(P === 0) /\ in(P, B) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> K </k>
        <heap> graph(P, B)(G) H </heap>
        CfgItems
      </config>
      <form> Phi /\ ~(P === 0) /\ ~ in(P, B) </form>
      TaskItems
    </task>
  )
  [structural]


  rule
    <heap_> graph(0, B)(G) => .Map <_/heap>
    <form> Phi => Phi /\ G === emptyGraph </form>
  [structural]
  rule
    <heap_> graph(P, B)(G) => .Map <_/heap>
    <form> Phi /\ in(P, B) => Phi /\ in(P, B) /\ G === emptyGraph </form>
  [structural]

  rule
    <heap_> graph(P, B)(emptyGraph) => .Map <_/heap>
    <form> Phi => Phi /\ (P === 0 \/ ~(P === 0) /\ in(P, B)) </form>
  [structural]


  rule
    <taskType> Run </taskType>
    <heap_>
        graph(P, B)(G)
      =>
        P |-> FreeInt(N) : (id("graphNode").id("mark"))
        (P +Int 1) |-> FreeInt(N +Int 1) : (id("graphNode").id("left"))
        (P +Int 2) |-> FreeInt(N +Int 2) : (id("graphNode").id("right"))
        graph(FreeInt(N +Int 1), B)(FreeGraph(N +Int 3))
        graph(FreeInt(N +Int 2), )(FreeGraph(N +Int 4))
    <_/heap>
    <counter> N => N +Int 5 </counter>
    <form>
        Phi /\ (P === 0) /\ (G === emptyGraph)
      =>
        Phi /\ ~(P === 0)
        /\ Tau === (FreeTree(N +Int 3) [[P] @ [FreeInt(N)]] FreeTree(N +Int 4))
    </form>
  [structural]


*** Syntactic sugar for Points-to Graphs ***
  rule graph(S)(G) => graph(S, {| 0 |}s)(G) [structural] 
endkm

