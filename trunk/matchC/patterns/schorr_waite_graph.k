/* 
 * Definition of points-to graphs
 * */


kmod SCHORR-WAITE-GRAPH-HP is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-SEQUENCE-BUILTIN-MODULE
          + MATHEMATICAL-GRAPH-BUILTIN-MODULE


  kvar N : Nat
  kvar Phi : Formula
  kvar P P1 P2 Q Q1 Q2 : Int++
  kvar I : Int++
  kvar S S1 S2 B B1 B2 : Set++
  kvar G G1 G2 : Graph
  kvar K TaskType : K
  kvar CfgItems TaskItems : Bag
  kvar H : Map


/* 
 * Derive case analysis:
 * - P belongs to the frontier
 * - P does not belong to the frontier
 */
  rule
    <task>
      <taskType> Run </taskType>
      <config>
        <k> derive(P) ~> K </k>
        <heap> graph(({| P |}s Us S), B)(G) H </heap>
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
        <heap> graph(({| P |}s Us S), B)(G) H </heap>
        CfgItems
      </config>
      <form> Phi /\ in(P, B) </form>
      TaskItems
    </task>
    <task>
      <taskType> Run </taskType>
      <config>
        <k> K </k>
        <heap> graph(({| P |}s Us S), B)(G) H </heap>
        CfgItems
      </config>
      <form> Phi /\ ~ in(P, B) </form>
      TaskItems
    </task>
  [structural]


  /*
   * Cases for deriving more concrete patterns from more abstract ones
   */
***(
  // the pattern is empty if the root set is empty
  rule
    <taskType> Run </taskType>
    <heap_> graph(S, B)(G) => .Map <_/heap>
    <form>
      Phi => Phi /\ subset(S, B) /\ G === (| S, emptySet |)
    </form>
  if Phi =/=Bool FalseFormula and-then checkForm(Phi ===> subset(S, B))
  [structural]
  // the pattern is empty if the graph abstraction is empty
  rule
    <taskType> Run </taskType>
    <heap_> graph(S, B)(G) => .Map <_/heap>
    <form>
      Phi => Phi /\ subset(S, B)  /\ G === (| S, emptySet |)
    </form>
  if Phi =/=Bool FalseFormula and-then checkForm(Phi ===> V(G) === S)
  [structural]

  // the pattern abstracts a heap object and another pattern
  rule
    <taskType> Run </taskType>
    <heap_>
        graph(({| P |}s Us S), B)(G)
      =>
        P |-> FreeInt(N) : (id("graphNode").id("mark"))
        (P +Int 1) |-> FreeInt(N +Int 1) : (id("graphNode").id("left"))
        (P +Int 2) |-> FreeInt(N +Int 2) : (id("graphNode").id("right"))
        graph
          ((S Us {| FreeInt(N +Int 1), FreeInt(N +Int 2) |}s), (B Us {| P |}s))
          ((| FreeSet(N +Int 3), FreeSet(N +Int 4) |))
    <_/heap>
    <counter> N => N +Int 7 </counter>
    <form>
        Phi
      =>
        Phi /\ ~ in(P, B)
        /\ FreeSet(N +Int 5)
           === {| v(P, [P] @ [FreeInt(N)]) |}s Us
               diff(FreeSet(N +Int 3), {| P |})s
        /\ FreeSet(N +Int 6)
           === {| e(P, FreeInt(N +Int 1), 0) |}s Us
               {| e(P, FreeInt(N +Int 2), 1) |}s Us
               FreeSet(N +Int 4)
        /\ G === (| FreeSet(N +Int 5), FreeSet(N +Int 6) |)
    </form>
  if Phi =/=Bool FalseFormula and-then checkForm(Phi ===> ~ in(P, B))
  [structural]
***)
  // the pattern is empty if the root set is empty
  rule
    <heap_> graph(S, S Us B)(G) => .Map <_/heap>
    <form>
      Phi => Phi /\ G === (| diff(S, {| 0 |}s), emptySet |)
    </form>
  [structural]
***(
  // the pattern is empty if the graph abstraction is empty
  rule
    <heap_> graph(S, B)((| V, emptySet |)) => .Map <_/heap>
    <form>
      Phi => Phi /\ subset(S, B)
    </form>
  if 
  [structural]
***)

  // the pattern abstracts a heap object and another pattern
  rule
    <taskType> Run </taskType>
    <heap_>
        graph(({| P |}s Us S), B)(G)
      =>
        P |-> FreeInt(N) : (id("graphNode").id("mark"))
        (P +Int 1) |-> FreeInt(N +Int 1) : (id("graphNode").id("left"))
        (P +Int 2) |-> FreeInt(N +Int 2) : (id("graphNode").id("right"))
        graph
          ((S Us {| FreeInt(N +Int 1), FreeInt(N +Int 2) |}s), (B Us {| P |}s))
          ((| FreeSet(N +Int 3), FreeSet(N +Int 4) |))
    <_/heap>
    <counter> N => N +Int 7 </counter>
    <form>
        Phi
      =>
        Phi /\ ~ in(P, B)
        /\ FreeSet(N +Int 5)
           === {| v(P, [P] @ [FreeInt(N)]) |}s Us
               diff(FreeSet(N +Int 3), {| P |}s)
        /\ FreeSet(N +Int 6)
           === {| e(P, FreeInt(N +Int 1), 0) |}s Us
               {| e(P, FreeInt(N +Int 2), 1) |}s Us
               FreeSet(N +Int 4)
        /\ G === (| FreeSet(N +Int 5), FreeSet(N +Int 6) |)
    </form>
  if Phi =/=Bool FalseFormula and-then VALID(Phi ===> ~ in(P, B))
  [structural]


  /*
   * Cases for deriving more abstract patterns from more concrete ones
   * TODO: incomplete
   */
  rule
    <taskType> TaskType </taskType>
    <heap_>
        graph(S, ({| 0 |}s Us B))(G)
      =>
        graph(({| 0 |}s Us S), ({| 0 |}s Us B))(G)
    <_/heap>
  if (TaskType ==Bool Hypothesis or-else TaskType ==Bool Conclusion) and-then
     in(0, S) =/=Bool TrueFormula
  //[structural]
***(
  rule
    <taskType> TaskType </taskType>
    <heap_>
        graph(S, ({| P |}s Us B))(G)
      =>
        graph
          (({| P |}s Us S), ({| P |}s Us B))
          ((| ({| P |}s Us V(G)), E(G) |))
    <_/heap>
    <form> Phi </form>
  if (TaskType ==Bool Hypothesis or-else TaskType ==Bool Conclusion) and-then
     checkForm(Phi ===> ~(P === 0) /\ ~ in(P, S))
  //[structural]
***)

  rule
    <taskType> Hypothesis </taskType>
    <heap_>
        P |-> I : (id("graphNode").id("mark"))
        (P +Int 1) |-> Q1 : (id("graphNode").id("left"))
        (P +Int 2) |-> Q2 : (id("graphNode").id("right"))
        graph(({| Q1 |}s Us {| Q2 |}s Us S), ({| P |}s Us B))(G)
      =>
        graph((S Us {| P |}s), B)
               ((| (diff(V(G), {| P |}s) Us {| v(P, [P] @ [I]) |}s),
                   E(G) Us {| e(P, Q1, 0) |}s Us {| e(P, Q2, 1) |}s
               |))
    <_/heap>
  // if in(P, S) =/=Bool TrueFormula


*** Syntactic sugar for Points-to Graphs ***
  rule graph(S)(G) => graph(S, {| 0 |}s)(G) [structural]
endkm

