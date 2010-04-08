INPUT = factorial
TEST_PROGRAMS = multWithBreak simplest sumn factorial hard
TMP = tmp
EXTENSION = .c

C_DIR = programs
SEMANTICS_DIR = semantics
PARSER_DIR = parser

CIL_BASE = cil
CIL_PLATFORM = x86_LINUX
GCC = /cygwin/bin/gcc-3
OCAMLOPT_FLAGS = -w a -warn-error a
CIL_FLAGS = --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused 

CIL = $(CIL_BASE)/obj/$(CIL_PLATFORM)

OCAML_COMPILE = ocamlopt $(OCAMLOPT_FLAGS) -c -I $(CIL) -I $(PARSER_DIR)
OCAML_LINK = ocamlopt $(OCAMLOPT_FLAGS) -ccopt -L$(CIL)

.SECONDARY:

all: cparser $(addsuffix .gen.program.maude,$(TEST_PROGRAMS))

$(TMP)/%.embed.c: $(C_DIR)/%.c Makefile
	mkdir -p $(TMP)
	perl embed.pl -d=ML -o=$@ $<

$(TMP)/%.preprocessed: $(TMP)/%.embed.c Makefile
	gcc -E -I. -o $@ $<

$(PARSER_DIR)/maudeVisitor.cmx $(PARSER_DIR)/maudeVisitor.cmi: $(PARSER_DIR)/maudeVisitor.ml
	$(OCAML_COMPILE) $(PARSER_DIR)/maudeVisitor.ml
	
$(PARSER_DIR)/maudePrinter.cmx $(PARSER_DIR)/maudePrinter.cmi: $(PARSER_DIR)/maudePrinter.ml $(PARSER_DIR)/defaultMaudePrinter.cmi
	$(OCAML_COMPILE) $(PARSER_DIR)/maudePrinter.ml
	
$(PARSER_DIR)/defaultMaudePrinter.cmx $(PARSER_DIR)/defaultMaudePrinter.cmi: $(PARSER_DIR)/defaultMaudePrinter.ml
	$(OCAML_COMPILE) $(PARSER_DIR)/defaultMaudePrinter.ml
	
$(PARSER_DIR)/cildriver.cmx $(PARSER_DIR)/cildriver.cmi: $(PARSER_DIR)/cildriver.ml $(PARSER_DIR)/maudeVisitor.cmi $(PARSER_DIR)/maudePrinter.cmi
	$(OCAML_COMPILE) $(PARSER_DIR)/cildriver.ml 

cparser: $(PARSER_DIR)/maudeVisitor.cmx $(PARSER_DIR)/maudePrinter.cmx $(PARSER_DIR)/cildriver.cmx
	$(OCAML_LINK) -o cparser unix.cmxa str.cmxa $(CIL)/cil.cmxa $(PARSER_DIR)/maudeVisitor.cmx $(PARSER_DIR)/defaultMaudePrinter.cmx $(PARSER_DIR)/maudePrinter.cmx $(PARSER_DIR)/cildriver.cmx
	
%.gen.program.maude: $(TMP)/%.preprocessed cparser
	./cparser $(CIL_FLAGS) --out $@ $<
	tail $@
	
$(SEMANTICS_DIR)/input-program.maude: c-maude.template $(INPUT).gen.program.maude
	printf "`cat c-maude.template`" "INPUT-PROGRAM" "`cat $(INPUT).gen.program.maude`" > $(SEMANTICS_DIR)/input-program.maude
	
$(SEMANTICS_DIR)/kernel-c-compiled.maude: $(SEMANTICS_DIR)/kernel-c-syntax.maude $(SEMANTICS_DIR)/kernel-c-semantics.maude $(SEMANTICS_DIR)/kernel-c.maude $(SEMANTICS_DIR)/input-program.maude
	make -C $(SEMANTICS_DIR)
	
.PHONY: semantics
semantics: $(SEMANTICS_DIR)/kernel-c-compiled.maude

test: test-aux

test-aux: semantics $(SEMANTICS_DIR)/test.maude
	maude $(SEMANTICS_DIR)/test.maude

# %.gen.maude: %.gen.program.maude
# echo -e "load $(K_BASE_DIR)/full-k-prelude\nload c-syntax\n" | cat - $< > $@.1
# echo -e "in c-configuration\nin c-semantics\nin c-test\n(rew run(program) .)\nq" | cat $@.1 - > $@
		
# c-core-raw.txt: generate-core-raw.maude Main.maude
# echo -e "load $(K_BASE_DIR)/full-k-prelude\n" | cat - generate-core-raw.maude | maude -no-banner -no-advise -no-wrap > c-core-raw.txt

run: $(INPUT).gen.maude.run

# %.gen.maude.run: %.gen.maude
# maude $<
	
# Main.maude:: c-syntax.maude c-configuration.maude c-semantics.maude

clean:
	rm -f $(PARSER_DIR)/*.cmi $(PARSER_DIR)/*.cmx $(PARSER_DIR)/*.o $(PARSER_DIR)/*.cil *.gen.* *.preprocessed cparser.exe cparser *.stackdump $(SEMANTICS_DIR)/kernel-c-compiled.maude $(TMP)/*
