load matchC-syntax
load matchC-semantics
load ../lib/fol
load ../patterns/list
load ../patterns/binary_tree
load ../patterns/binary_height_tree
load ../patterns/schorr_waite_binary_tree
load ../patterns/io
load ../patterns/stack


kmod MATCHC is
  including MATCHC-SEMANTICS
          + MATHEMATICAL-DOMAIN-BUILTIN-MODULE
          + FOL
          + LIST-HP
          + BINARY-TREE-HP
          + BINARY-HEIGHT-TREE-HP
          + SCHORR-WAITE-BINARY-TREE-HP
          + IO-PATTERN
          + STACK-PATTERN


  kvar N M : Nat
  kvar I : Int
  kvar S : String
  kvar L : List


  syntax BagItem ::= check ( K )
                   | ( Nat feasible and Nat infeasible paths)

  macro check(K:K) = <top_>
                       //<check> SetItem(checkContract(id("main"))) </check>
                       <check> .Set </check>
                       <program> K:K ~> checkContracts </program>
                       <k> disolveTask </k>
                     <_/top>


***(
Output
***)
  rule
    <feasible> I => I +Int 1 </feasible>
    (
      <task_>
        <program> .K </program>
        <k> disolveTask </k>
      <_/task>
    =>
      .Bag
    )
  [structural]
  rule
    <infeasible> I => I +Int 1 </infeasible>
    (
      <task_>
        <form> FalseFormula </form>
      <_/task>
    =>
      .Bag
    )
  [structural]
  rule
    <funTask>
      <funId> .K </funId>
    </funTask>
  =>
    .Bag
  [structural]
  rule
    <funTask>
      <funId> id(S) </funId>
    </funTask>
  =>
    .Bag
  [structural]
  rule
    <tasks> .Bag </tasks>
  =>
    .Bag 
  [structural]
  rule
    <feasible> I => I +Int 1 </feasible>
    <mainOut> .List => L </mainOut>
    <tasks_>
        <funTask>
          <funId> id("main") </funId>
          <task_>
            <program> .K </program>
            <k> .K </k>
            <out> L </out>
          <_/task>
        </funTask>
      =>
        .Bag
    <_/tasks>
  [structural]


  syntax Map ::= labelHeap ( Int++ , Nat , Seq++ , Id , List{KernelC} , Nat )
  rule
    <struct_> X:Id |-> fieldList(KernelCList:List{KernelC}) <_/struct>
    <heap_>
        ?var(V:Id) |-> A:Seq++
      =>
        labelHeap(?var(V:Id), 0, A:Seq++, X:Id, KernelCList:List{KernelC}, 0)
    <_/heap>
    <tenv_> V:Id |-> struct X:Id* <_/tenv>
  [structural]
  rule
    <struct_> X:Id |-> fieldList(KernelCList:List{KernelC}) <_/struct>
    <heap_>
        ?var(V:Id) +Int N |-> A:Seq++
      =>
        labelHeap(?var(V:Id), N, A:Seq++, X:Id, KernelCList:List{KernelC}, 0)
    <_/heap>
    <tenv_> V:Id |-> struct X:Id* <_/tenv>
  [structural]
  rule
    <struct_> X:Id |-> fieldList(KernelCList:List{KernelC}) <_/struct>
    <heap_>
        !var(V:Id) |-> A:Seq++
      =>
        labelHeap(!var(V:Id), 0, A:Seq++, X:Id, KernelCList:List{KernelC}, 0)
    <_/heap>
    <tenv_> V:Id |-> struct X:Id* <_/tenv>
  [structural]
  rule
    <struct_> X:Id |-> fieldList(KernelCList:List{KernelC}) <_/struct>
    <heap_>
        !var(V:Id) +Int N |-> A:Seq++
      =>
        labelHeap(!var(V:Id), N, A:Seq++, X:Id, KernelCList:List{KernelC}, 0)
    <_/heap>
    <tenv_> V:Id |-> struct X:Id* <_/tenv>
  [structural]
  rule
    <struct_> X:Id |-> fieldList(KernelCList:List{KernelC}) <_/struct>
    <heap_>
        FreeVar(V:Id) |-> A:Seq++
      =>
        labelHeap(FreeVar(V:Id), 0, A:Seq++, X:Id, KernelCList:List{KernelC}, 0)
    <_/heap>
    <tenv_> V:Id |-> struct X:Id* <_/tenv>
  [structural]
  rule
    <struct_> X:Id |-> fieldList(KernelCList:List{KernelC}) <_/struct>
    <heap_>
        FreeVar(V:Id) +Int N |-> A:Seq++
      =>
        labelHeap(FreeVar(V:Id), N, A:Seq++, X:Id, KernelCList:List{KernelC}, 0)
    <_/heap>
    <tenv_> V:Id |-> struct X:Id* <_/tenv>
  [structural]
/*
  rule
    <struct_> X:Id |-> fieldList(KernelCList:List{KernelC}) <_/struct>
    <heap_>
        co-skolem(M, FreeVar(V:Id)) |-> A:Seq++
      =>
        labelHeap(co-skolem(M, FreeVar(V:Id)), 0, A:Seq++
                  X:Id, KernelCList:List{KernelC}, 0)
    <_/heap>
    <tenv_> V:Id |-> struct X:Id* <_/tenv>
  [structural]
  rule
    <struct_> X:Id |-> fieldList(KernelCList:List{KernelC}) <_/struct>
    <heap_>
        co-skolem(M, FreeVar(V:Id)) +Int N |-> A:Seq++
      =>
        labelHeap(co-skolem(M, FreeVar(V:Id)), N, A:Seq++,
                  X:Id, KernelCList:List{KernelC}, 0)
    <_/heap>
    <tenv_> V:Id |-> struct X:Id* <_/tenv>
  [structural]
*/
  rule labelHeap(_, N, _, _, (_:KernelC => .List{KernelC}),,,_, (M => sNat M))
  if M <Int N [structural]
  rule
      labelHeap(P:Int++, N, ([Q:Int++] @ A:Seq++),
                X:Id, ((_ F:Id;),,, KernelCList:List{KernelC}), N)
    =>
      P:Int++ +Int N |-> Q:Int++ : X.F
      labelHeap(P:Int++, sNat N, A:Seq++,
                X:Id, KernelCList:List{KernelC}, sNat N)
  [structural]
  rule labelHeap(_, _, epsilon, _, _, _) => .Map [structural]
endkm

