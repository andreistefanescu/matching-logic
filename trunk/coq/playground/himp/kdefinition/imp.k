module IMP-SYNTAX
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, seqstrict]
                 > AExp "+" AExp              [left, seqstrict]
                 | AExp "-" AExp              [left, seqstrict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Stmt  ::= "skip"
                 | "(" Stmt ")"               [bracket]
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Stmt "else" Stmt         [strict(1)]
                 | "while" "(" BExp ")" Stmt
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "var" Id "is" Int "in" Stmt
endmodule

module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool

  configuration <T color="yellow">
  		  <k color="green"> $PGM:Pgm </k>
		  <state color="red"> .Map </state>
		</T>

// AExp
  rule <k> X:Id => I ...</k> <state>... X |-> I ...</state>
  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  rule I1:Int + I2:Int => I1 +Int I2
  rule I1:Int - I2:Int => I1 -Int I2
// BExp
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule ! T:Bool => notBool T
  rule true && B => B
  rule false && _ => false
// Stmt
  rule skip => .   [structural]
  rule <k> X = I:Int; => . ...</k> <state>... X |-> (_ => I) ...</state>
  rule S1 S2 => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule while (B) S => if (B) (S while (B) S) else skip  [structural]
// Pgm
  rule <k> var X is I in S => S </k> <state> . => (X |-> I) </state>
endmodule