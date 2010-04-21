CIL_BASE = ../cil
CIL_PLATFORM = x86_LINUX
OCAMLOPT_FLAGS = -w a -warn-error a

CIL = $(CIL_BASE)/obj/$(CIL_PLATFORM)

OCAML_COMPILE = ocamlopt $(OCAMLOPT_FLAGS) -c -I $(CIL)
OCAML_LINK = ocamlopt $(OCAMLOPT_FLAGS) -I $(CIL) -ccopt -L$(CIL)
 
.PHONY: all cleanOnMakefileChange clean
all: cparser 

maudeVisitor.cmx maudeVisitor.cmi: maudeVisitor.ml
	$(OCAML_COMPILE) maudeVisitor.ml
	
maudePrinter.cmx maudePrinter.cmi: maudePrinter.ml defaultMaudePrinter.cmi
	$(OCAML_COMPILE) maudePrinter.ml
	
defaultMaudePrinter.cmx defaultMaudePrinter.cmi: defaultMaudePrinter.ml
	$(OCAML_COMPILE) defaultMaudePrinter.ml
	
cildriver.cmx cildriver.cmi: cildriver.ml maudeVisitor.cmi maudePrinter.cmi
	$(OCAML_COMPILE) cildriver.ml 

cparser: maudeVisitor.cmx defaultMaudePrinter.cmx maudePrinter.cmx cildriver.cmx 
	$(OCAML_LINK) -o cparser unix.cmxa str.cmxa cil.cmxa maudeVisitor.cmx defaultMaudePrinter.cmx maudePrinter.cmx cildriver.cmx


clean:
	rm -f *.cmi *.cmx *.o *.cil *.preprocessed cparser.exe cparser *.stackdump
