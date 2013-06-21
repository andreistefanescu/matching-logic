/*!
\title{Low-Level Program Verification using Matching Logic Reachability}
\author{Dwight Guth, Andrei \c{S}tef\u{a}nescu, and Grigore Ro\c{s}u}
\organization{University of Illinois at Urbana-Champaign}
*/

module WCET-SYNTAX
  //@ \K definitions are organized into a group of semi-independent modules.


  syntax BInst ::= BOpCode Register "," Exp "," Exp [klabel('binst), strict(3, 4)]
  /*@ \K defines its own syntax: the user declares the syntax of the programming language being
  defined, and then uses it later on in rules. */

  syntax BOpCode ::= "add" | "sub" | "mul" | "div" | "or" | "and"
  syntax Exp ::= Register
               | "#" Int
  syntax Register ::= "r" Int
  /*@ These productions define the basic pieces of B-Type instructions in the language. The
  language is a 3-register language, so each instruction has two sources and one target.

  The language has two indexing modes: an integer may signify the contents of a numbered register,
  or it may be an immediate value. Here, the non-terminal Int corresponds to the pre-existing
  algebra of arbitrary-precision integers.*/

  syntax UInst ::= UOpCode Register "," Exp [klabel('uinst), strict(3)]
  syntax UOpCode ::= "not"
  /*@ Some productions are tagged with an attribute, \kattribute{strict}, which takes a
  comma-separated list of integers. \K is based partially on the chemical abstract machine.
  Expressions are \textbf{heated} out of productions, evaluated to values, and then \textbf{cooled}
  back into the production to be rewritten further. The integer arguments specify a set of
  non-terminals to be heated and cooled.
  */

  syntax MInst ::= MOpCode Exp "," Exp [klabel('minst), strict(2, 3)]
  syntax UOpCode ::= "load"
  syntax MOpCode ::= "store"
  /*@ In addition to basic arithmetic and bitwise-logical operations, our language supports load
  and store operations to index memory dynamically. Load evaluates a memory location into a
  register; store evaluates a memory location and a value and puts the value into memory.*/

  syntax JInst ::= JOpCode Id [klabel('jinst)]
  syntax JOpCode ::= "jmp"

  syntax BrInst ::= BrOpCode Id "," Exp "," Exp [klabel('brinst), strict(3, 4)]
  syntax BrOpCode ::= "beq" | "bne" | "blt" | "ble"
  //@ The language also supports basic conditional and unconditional jump instructions ...

  syntax NInst ::= NOpCode
  syntax NOpCode ::= "halt"
  //@ ... And terminating execution ...

  syntax SInst ::= SOpCode Exp [klabel('sinst), strict(2)]
  syntax SOpCode ::= "sleep"
  //@ ... And real-time instructions from the basic (sleep for a specified number of cycles) ...

  syntax RInst ::= ROpCode Register "," Id [klabel('rinst)]
  syntax ROpCode ::= "read"

  syntax WInst ::= WOpCode Id "," Exp [klabel('winst), strict(3)]
  syntax WOpCode ::= "write"

  syntax RWInst ::= RWOpCode Register "," Id "," Exp [klabel('rwinst), strict(4)]
  syntax RWOpCode ::= "rw"
  /*@ ... To the not so basic: read and write I/O from a named bus, or perform both atomically in
  sequence. */

  syntax BrOpCode ::= "int"
  syntax NOpCode ::= "rfi"
  /*@ Finally, we support periodic timer interrupts. The \texttt{int} instruction schedules an
  interrupt, which fires periodically until the program is terminated. The \texttt{rfi} instruction
  returns from an interrupt. */

  syntax UOpCode ::= "li"
  syntax BrOpCode ::= "bgt" | "bge"
  rule li R:Register , E:Exp => or R , E , #0 [macro]

  rule bgt X:Id , E:Exp , E2:Exp => blt X , E2 , E [macro]
  rule bge X:Id , E:Exp , E2:Exp => ble X , E2 , E [macro]
  /*@ We also define a couple convenience instructions as macros: a macro is applied statically,
  and its semantics correspond exactly with the term it represents.*/

  syntax Id ::= "main"
  /*@ And we also declare the syntax for any alphanumeric identifiers we wish to use directly in
  the rules of our semantics.*/

  //@ Last, some stuff to glue operations together and provide alphanumeric labels to blocks.
  syntax Inst ::= BInst | UInst | MInst | JInst | BrInst | NInst | SInst | RInst | WInst | RWInst
  syntax Insts ::= Inst | Inst Insts
  syntax Block ::= Id ":" Insts
  syntax Blocks ::= Block | Block Blocks

  syntax OpCode ::= BOpCode | UOpCode | MOpCode | JOpCode | BrOpCode | NOpCode | SOpCode | ROpCode | WOpCode | RWOpCode



endmodule

module WCET
  imports WCET-SYNTAX
  //@ Modules import other modules to include their syntax and operations into their own.

  configuration
    <T>
      <k> load($PGM:K) ~> jumpTo(main) </k>
      <pgm> .Map </pgm>
      <mem> .Map </mem>
      <reg> .Map </reg>
      <br/>
      <timing> $TIMING:Map </timing>
      <wcet> 0 </wcet>
      <input> $INPUT:List </input>
      <status> $INITIAL:Map </status>
      <timers> .List </timers>
      <br/>
      <priority> 0 </priority>
      <stack> .List </stack>
      <interrupts> .Set </interrupts>
    </T>
  /*@ An executing \K program keeps track of its internal state inside the \textbf{configuration}
  of the semantics. A configuration is a nested set of cells which can be referenced modularly in
  rules.  This declaration specifies the initial configuration of the program by means of several
  variables. These variables are initialized by the tool after being specified by the user on the
  command line. In particular, $\$PGM$ contains the AST of the program parsed from the file being
  executed. This initial configuration performs preprocessing on the program and then jumps to the
  entry point, labelled \texttt{main}.*/

  syntax KResult ::= Int
  /*@ We provide the special sort $KResult$ to know when a term is done evaluating and should be
  cooled.*/

  syntax Exp ::= Int
  /*@ We write partially-evaluated terms with their subterms evaluated using the same syntax for
  programs, so we need integers, the result type, to be an expression.*/

  syntax K ::= load(K)
             | jumpTo(Id)
  /*@ The semantics is free to define additional operators to use internally. Because they are not
  part of WCET-SYNTAX module, they cannot be used in programs.*/

  rule <k> I:Inst Is:Insts => I ~> Is ...</k>
  /*@ The \texttt{k} cell in the configuration stores the currently executing computation. This 
  simple rule says to evaluate a list of instructions by means of sequential composition. The
  jagged edge of the cell on the right side indicates that this rule can match any prefix of the
  entire \texttt{k} cell, not just if the term is the only present. The term below the line
  corresponds to the right hand side of a rewrite operation.*/

  rule load(B:Block Bs:Blocks) => load(B) ~> load(Bs)
  rule <k> load(X:Id : Is:Insts) => . ...</k>
       <pgm>... . => X |-> (Is) ...</pgm>

  rule <k> jumpTo(X) ~> _ => K </k>
       <pgm>... X:Id |-> K:K ...</pgm>
  /*@ Jumping from one block to the next is defined by storing each block in a map in the
  \texttt{pgm} cell in the configuration. So we initialize this value before executing the program,
  and a jump simply consists of replacing the entire \texttt{k} cell with the new block. Note a
  rule operating only on a prefix of the \texttt{k} cell can be written without a bubble.*/

  rule <k> r I:Int => I2:Int ...</k>
       <reg>... I |-> I2 ...</reg>
  //@ Register lookup looks up the numbered register in the \texttt{reg} cell.

  rule # I:Int => I
  //@ And an immediate evaluates to its own declared value.

  rule <k> add r I:Int , I2:Int , I3:Int => time(add) ...</k>
       <reg> R:Map => R[I2 +Int I3 / I] </reg>
  rule <k> sub r I:Int , I2:Int , I3:Int => time(sub) ...</k>
       <reg> R:Map => R[I2 -Int I3 / I] </reg>
  rule <k> mul r I:Int , I2:Int , I3:Int => time(mul) ...</k>
       <reg> R:Map => R[I2 *Int I3 / I] </reg>
  rule <k> div r I:Int , I2:Int , I3:Int => time(div) ...</k>
       <reg> R:Map => R[I2 /Int I3 / I] </reg>
  rule <k> or r I:Int , I2:Int , I3:Int => time(or) ...</k>
       <reg> R:Map => R[I2 |Int I3 / I] </reg>
  rule <k> and r I:Int , I2:Int , I3:Int => time(and) ...</k>
       <reg> R:Map => R[I2 &Int I3 / I] </reg>
  rule <k> not r I:Int , I2:Int => time(not) ...</k>
       <reg> R:Map => R[~Int I2 / I] </reg>
  /*@ The first instructions of the language are defined above. Once the arguments are evaluated,
  arithmetic operation is performed and stored in the target register. Then the time of the
  instruction is made to elapse. The auxiliary operation \texttt{time} elapses time according to
  the specified length of the instruction in question.*/

  rule <k> load r I:Int , I2:Int => time(load) ...</k>
       <mem>... I2 |-> I3:Int ...</mem>
       <reg> R:Map => R[I3 / I] </reg>
  /*@ The \texttt{mem} cell contains memory. An integer location in memory is evaluated, indexed in
  memory, and the value found there is put in a register.*/

  rule <k> store I:Int , I2:Int => time(store) ...</k>
       <mem> M:Map => M[I2 / I] </mem>
  //@ \texttt{store} operates on the same principle, except it performs a map update operation.

  rule jmp X:Id => time(jmp) ~> jumpTo(X)
  //@ Unconditional jump jumps to a new block ...
  rule <k> beq X:Id , I:Int , I2:Int => time(beq) ~> branch(I ==Int I2, X)  ...</k>
  rule <k> bne X:Id , I:Int , I2:Int => time(bne) ~> branch(I =/=Int I2, X) ...</k>
  rule <k> blt X:Id , I:Int , I2:Int => time(blt) ~> branch(I <Int I2, X) ...</k>
  rule <k> ble X:Id , I:Int , I2:Int => time(ble) ~> branch(I <=Int I2, X) ...</k>

  syntax K ::= branch(Bool, Id)
  rule branch(true, X:Id) => jumpTo(X)
  rule branch(false, _) => .
  //@ ... And conditional jump evaluates a boolean condition and jumps if the condition is true.

  rule halt ~> _ => time(halt)
  /*@ \texttt{halt} removes the entire \texttt{k} cell, effectively ending execution (once it is finished
  executing)*/

  rule sleep I:Int => waitFor(I)
  //@ The auxiliary operation \texttt{waitFor} elapses a specified length of time.

  rule <k> read r I:Int , X:Id => time(read) ...</k>
       <status>... X |-> I2:Int ...</status>
       <reg> Reg:Map => Reg[I2 / I] </reg>
  /*@ An I/O read looks up the current value of the data in the \texttt{status} cell, then
  writes it to a register.*/

  rule <k> write X:Id , I:Int => time(write) ...</k>
       <status> Status:Map => Status[I / X] </status>
  //@ \texttt{write} does the same in reverse ...

  rule <k> rw r I:Int , X:Id , I3:Int => time(rw) ...</k>
       <status>... X |-> (I2:Int => I3) ...</status>
       <reg> Reg:Map => Reg[I2 / I] </reg>
  //@ ... And \texttt{rw} performs both at the same instant.

  syntax K ::= (Id, Int, Int)
  rule <k> int X:Id , I:Int , I2:Int => time(int) ...</k>
       <timers>... . => ListItem((X, I +Int Time, I2)) </timers>
       <wcet> Time:Int </wcet>
  /*@ \texttt{int} schedules an interrupt $I$ cycles after executing, to execute periodically every
  $I2$ cycles thereafter. The \texttt{timers} cell stores the currently activated interrupts in a
  list of tuples.*/

  syntax K ::= (K, Int)
  rule <k> rfi ~> _ => time(rfi) ~> K </k>
       <stack> ListItem((K:K, Priority:Int)) => . ...</stack>
       <priority> _ => Priority </priority>
  /*@ To return from an interrupt, we restore the previously executing code from the \texttt{stack}
  cell, which also contains the previously-executing priority to restore to the \texttt{priority}
  cell.  Interrupts are assigned numeric priority in the order they are scheduled by the program,
  and can interrupt only code running at a lower priority. Recall the program begins executing at
  priority 0.*/

  syntax K ::= time(OpCode)
  rule <k> time(O:OpCode) => waitFor(Timing(O)) ...</k>
       <timing> Timing:Map </timing>
  /*@ For modularity, we allow the time each instruction executes for to be specified dynamically
  in the \texttt{timing} cell.*/

  syntax K ::= waitFor(Int)
  rule <k> waitFor(I:Int) => updateStatus(I2) ~> updateTimers(L) ~> interrupt(L, lengthList L) ...</k>
       <br/>
       <wcet> I2:Int => I2 +Int I </wcet>
       <timers> L:List => . </timers>
  /*@ The \texttt{wcet} cell stores the length of time the program has already been running for, in
  total. When time passes, two types of asynchronous events can occur. The first is a write on an
  I/O line, provided in advance in the \texttt{input} cell. The second is the firing of a timer 
  interrupt.*/

  syntax K ::= updateStatus(Int)
  syntax K ::= (Int, Map)
  rule <k> updateStatus(Start:Int) ...</k>
       <input> ListItem((I2:Int, M:Map)) => . ...</input>
       <wcet> I:Int </wcet>
       <status> Status:Map => Status[M] </status> when I >=Int I2 andBool I2 >=Int Start
  rule <k> updateStatus(Start:Int) => . ...</k>
       <input> ListItem((I2:Int, _)) ...</input>
       <wcet> I:Int </wcet> when notBool(I >=Int I2 andBool I >=Int Start)
  rule <k> updateStatus(_) => . ...</k>
       <input> .List </input>
  /*@ The above rules are somewhat technical, but to summarize, every data write occurring during 
  the time period being elapsed is popped from the \texttt{input} cell and written to the
  \texttt{status} cell.*/

  syntax K ::= updateTimers(List)
  rule <k> updateTimers((ListItem((X:Id, Expires:Int, Interval:Int)) => .) _) ...</k>
       <br/>
       <wcet> I:Int </wcet>
       <timers>... . => ListItem((X, Expires, Interval)) </timers> when I <Int Expires orBool Interval ==Int 0
  rule <k> updateTimers(ListItem((X:Id, (Expires:Int => Expires +Int Interval), Interval:Int)) _) ...</k>
       <br/>
       <wcet> I:Int </wcet>
       <interrupts>... . => SetItem(X) </interrupts> when I >=Int Expires andBool Interval =/=Int 0
  rule updateTimers(.List) => .
  /*@ Once again, to summarize, all interrupts that are triggered during the elapsed period of
  time have their interrupt flag set by adding their name to the \texttt{interrupts} cell.*/

  syntax K ::= interrupt(List, Int)
  rule <k> interrupt((ListItem((X:Id, _, _)) => .) _, (N:Int => N -Int 1)) ...</k>
       <br/>
       <interrupts> S:Set </interrupts>
       <priority> Priority:Int </priority> when notBool(X in S) orBool N <=Int Priority
  rule <k> interrupt(ListItem((X:Id, _, _)) _, N:Int) ~> K:K => jumpTo(X) </k>
       <priority> Priority:Int => N </priority>
       <br/>
       <interrupts> S:Set => S -Set SetItem(X) </interrupts>
       <stack> . => ListItem((K, Priority)) ...</stack> when N >Int Priority andBool X in S
  rule <k> interrupt(.List, _) => . ...</k>
  /*@ Finally, to summarize, after the interrupt flags have been set, we jump to the highest
  priority interrupt that has fired, and begin executing, storing the previous computation and 
  priority in the \texttt{stack} cell. When we reach an \texttt{rfi} instruction, we will pop the
  stack and check for interrupts again. If all interrupts have been serviced, execution of normal
  code will resume.*/

endmodule
