INPUT = factorial
TEST_PROGRAMS = multWithBreak simplest sumn factorial
TMP = tmp
EXTENSION = .c

C_DIR = programs

CIL_BASE = cil
CIL_PLATFORM = x86_WIN32
GCC = /cygwin/bin/gcc-3
OCAMLOPT_FLAGS = -w a -warn-error a
CIL_FLAGS = --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused 

#K_BASE_DIR = /home/grosu/celliso2/k/trunk
K_BASE_DIR = ../..
#--stats 

CIL = $(CIL_BASE)/obj/$(CIL_PLATFORM)

OCAML_COMPILE = ocamlopt $(OCAMLOPT_FLAGS) -c -I $(CIL)
OCAML_LINK = ocamlopt $(OCAMLOPT_FLAGS) -ccopt -L$(CIL)

all: uglyprint $(addsuffix .gen.program.maude,$(TEST_PROGRAMS))

%.preprocessed: $(C_DIR)/%.c Makefile
	mkdir -p $(TMP)
	gcc -E -I. -o $(TMP)/$@ $<

MaudeVisitor.cmx MaudeVisitor.cmi: maudeVisitor.ml
	$(OCAML_COMPILE) maudeVisitor.ml
	
MaudePrinter.cmx MaudePrinter.cmi: maudePrinter.ml DefaultMaudePrinter.cmi
	$(OCAML_COMPILE) maudePrinter.ml
	
DefaultMaudePrinter.cmx DefaultMaudePrinter.cmi: defaultmaudePrinter.ml
	$(OCAML_COMPILE) defaultMaudePrinter.ml
	
cildriver.cmx cildriver.cmi: cildriver.ml MaudeVisitor.cmi MaudePrinter.cmi
	$(OCAML_COMPILE) cildriver.ml 

uglyprint: MaudeVisitor.cmx MaudePrinter.cmx cildriver.cmx
	$(OCAML_LINK) -o uglyprint unix.cmxa str.cmxa $(CIL)/cil.cmxa MaudeVisitor.cmx DefaultMaudePrinter.cmx MaudePrinter.cmx cildriver.cmx
	
%.gen.program.maude: %.preprocessed uglyprint
	uglyprint $(CIL_FLAGS) --out $@ $(TMP)/$<
	tail $@

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
	rm -f *.cmi *.cmx *.o *.cil *.gen.* *.preprocessed uglyprint.exe uglyprint *.stackdump
