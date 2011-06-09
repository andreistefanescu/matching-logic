tree grammar annotPass1;

options {
  tokenVocab = annot;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}


bottomup
  : program_identifier
  | program_variable
  | old_program_variable
  ;

program_identifier
  : id=PROGRAM_IDENTIFIER
    -> ^(BUILTIN["obj`(_`)"] ^(ID STRING_LITERAL["\"" + $id.text + "\""]))
  ;

program_variable
options { backtrack = true; }
  : id=PROGRAM_VARIABLE { !Table.varString.startsWith("!") }?
    -> ^(BUILTIN["FreeVar"]
         ^(ID["id"] STRING_LITERAL["\"" + $id.text + "\""]))
  | id=PROGRAM_VARIABLE { Table.varString.startsWith("!") }?
    -> ^(BUILTIN["?var"] ^(ID["id"] STRING_LITERAL["\"" + $id.text + "\""]))
  ;

/*
  | id=PRIME_IDENTIFIER
    -> ^(IDENTIFIER["?var"]
         ^(ID["id"] STRING_LITERAL["\"" + $id.text.replace("\'", "") + "\""]))
*/

old_program_variable
  : ^(old_wrapper=IDENTIFIER ^(var_wrapper=BUILTIN c=.))
    { "old".equals($old_wrapper.text) && "?var".equals($var_wrapper.text) }?
    -> ^(BUILTIN["FreeVar"] $c)
  ;

