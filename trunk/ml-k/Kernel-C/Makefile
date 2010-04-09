INPUT = sumn
#TEST_PROGRAMS = multWithBreak simplest sumn factorial hard
TMP = tmp

C_DIR = programs
SEMANTICS_DIR = semantics
PARSER_DIR = parser

CIL_FLAGS = --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused 

.SECONDARY:

.PHONY: all clean run test semantics test-aux

all: cparser 
#$(addsuffix .gen.program.maude,$(TEST_PROGRAMS))

$(PARSER_DIR)/cparser: Makefile
	make -C $(PARSER_DIR)

cparser: $(PARSER_DIR)/cparser Makefile
	cp $(PARSER_DIR)/cparser .

$(TMP)/%.embed.c: $(C_DIR)/%.c Makefile
	mkdir -p $(TMP)
	perl embed.pl -d=ML -o=$@ $<

$(TMP)/%.preprocessed: $(TMP)/%.embed.c Makefile
	gcc -E -I. -o $@ $<

$(TMP)/%.gen.program.maude: $(TMP)/%.preprocessed cparser
	./cparser $(CIL_FLAGS) --out $@ $<
	tail $@
	
dynamic-build: $(TMP)/$(INPUT).gen.program.maude
	make -C $(SEMANTICS_DIR) dynamic INPUT=$(realpath $<)

match-build: $(TMP)/$(INPUT).gen.program.maude
	make -C $(SEMANTICS_DIR) match INPUT=$(realpath $<)
	
test: dynamic-build $(SEMANTICS_DIR)/test.maude
	maude $(SEMANTICS_DIR)/test.maude
	
test-match: match-build $(SEMANTICS_DIR)/test.maude
	maude $(SEMANTICS_DIR)/test.maude

run: $(INPUT).gen.maude.run

clean:
	rm -f cparser $(TMP)/*
	make -C $(PARSER_DIR) clean
	make -C $(SEMANTICS_DIR) clean
