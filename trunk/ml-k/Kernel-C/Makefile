INPUT = factorial
TEST_PROGRAMS = multWithBreak simplest sumn factorial hard
TMP = tmp
EXTENSION = .c

C_DIR = programs
SEMANTICS_DIR = semantics
K-MAUDE = ../../../../k-framework/k-maude/trunk/tools/kcompile.sh
PARSER_DIR = parser

CIL_BASE = cil
CIL_PLATFORM = x86_WIN32
GCC = /cygwin/bin/gcc-3
OCAMLOPT_FLAGS = -w a -warn-error a
CIL_FLAGS = --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused 

#K_BASE_DIR = /home/grosu/celliso2/k/trunk
K_BASE_DIR = ../..
#--stats 

CIL = $(CIL_BASE)/obj/$(CIL_PLATFORM)

OCAML_COMPILE = ocamlopt $(OCAMLOPT_FLAGS) -c -I $(CIL) -I $(PARSER_DIR)
OCAML_LINK = ocamlopt $(OCAMLOPT_FLAGS) -ccopt -L$(CIL):$(PARSER_DIR)

all: cparser $(addsuffix .gen.program.maude,$(TEST_PROGRAMS))

%.preprocessed: $(C_DIR)/%.c Makefile
	mkdir -p $(TMP)
	gcc -E -I. -o $(TMP)/$@ $<

$(PARSER_DIR)/MaudeVisitor.cmx $(PARSER_DIR)/MaudeVisitor.cmi: $(PARSER_DIR)/maudeVisitor.ml
	$(OCAML_COMPILE) $(PARSER_DIR)/maudeVisitor.ml
	
$(PARSER_DIR)/MaudePrinter.cmx $(PARSER_DIR)/MaudePrinter.cmi: $(PARSER_DIR)/maudePrinter.ml $(PARSER_DIR)/DefaultMaudePrinter.cmi
	$(OCAML_COMPILE) $(PARSER_DIR)/maudePrinter.ml
	
$(PARSER_DIR)/DefaultMaudePrinter.cmx $(PARSER_DIR)/DefaultMaudePrinter.cmi: $(PARSER_DIR)/defaultmaudePrinter.ml
	$(OCAML_COMPILE) $(PARSER_DIR)/defaultMaudePrinter.ml
	
$(PARSER_DIR)/cildriver.cmx $(PARSER_DIR)/cildriver.cmi: $(PARSER_DIR)/cildriver.ml $(PARSER_DIR)/MaudeVisitor.cmi $(PARSER_DIR)/MaudePrinter.cmi
	$(OCAML_COMPILE) $(PARSER_DIR)/cildriver.ml 

cparser: $(PARSER_DIR)/MaudeVisitor.cmx $(PARSER_DIR)/MaudePrinter.cmx $(PARSER_DIR)/cildriver.cmx
	$(OCAML_LINK) -o cparser unix.cmxa str.cmxa $(CIL)/cil.cmxa $(PARSER_DIR)/MaudeVisitor.cmx $(PARSER_DIR)/DefaultMaudePrinter.cmx $(PARSER_DIR)/MaudePrinter.cmx $(PARSER_DIR)/cildriver.cmx
	
%.gen.program.maude: %.preprocessed cparser
	./cparser $(CIL_FLAGS) --out $@ $(TMP)/$<
	tail $@
	
semantics: $(SEMANTICS_DIR)/kernel-c.maude
	$(K-MAUDE) $(SEMANTICS_DIR)/kernel-c.maude KERNEL-C

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
	rm -f $(PARSER_DIR)/*.cmi $(PARSER_DIR)/*.cmx $(PARSER_DIR)/*.o $(PARSER_DIR)/*.cil *.gen.* *.preprocessed cparser.exe cparser *.stackdump
