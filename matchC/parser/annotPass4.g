tree grammar annotPass4;

options {
  tokenVocab = annot;
  output = AST;
  ASTLabelType = CommonTree;
  filter = true;
}


topdown
  : logical_variable
  ;

logical_variable
  : LOGICAL_VARIABLE -> BUILTIN[$LOGICAL_VARIABLE.text]
  ;

