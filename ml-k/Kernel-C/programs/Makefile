PARSER_DIR = ../parser
TEST_PROGRAMS = multWithBreak simplest sumn factorial hard listReverse
CIL_FLAGS = --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused 

.SECONDARY:

.PHONY: all clean benchmark

benchmark: $(addsuffix .gen.maude,$(TEST_PROGRAMS))

all: %.gen.maude

%.prepre.gen.c: %.c embed.pl Makefile
	perl embed.pl -d=ML -o=$@ $<

%.pre.gen.c: %.prepre.gen.c
	gcc -E -I. -o $@ $<

%.gen.maude: %.pre.gen.c $(PARSER_DIR)/cparser
	$(PARSER_DIR)/cparser $(CIL_FLAGS) --out $@ $<
	tail $@
		
clean:
	rm -f *.prepre.gen.c *.pre.gen.c *.gen.maude
