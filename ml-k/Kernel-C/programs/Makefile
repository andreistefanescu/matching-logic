PARSER_DIR = ../parser
PARSER = $(PARSER_DIR)/cparser
TEST_PROGRAMS = multWithBreak simplest sumn factorial hard listReverse

ALL_FILES = $(wildcard *.c)
ALL_PROGRAMS = $(basename $(ALL_FILES))
CIL_FLAGS = --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused 

#.SECONDARY:

.PHONY: all clean benchmark

all: $(addsuffix .gen.maude,$(ALL_PROGRAMS))

benchmark: $(addsuffix .gen.maude,$(TEST_PROGRAMS))

%.prepre.gen.c: %.c embed.pl Makefile
	@perl embed.pl -d=ML -o=$@ $<

%.pre.gen.c: %.prepre.gen.c
	@gcc -Wall -Wextra -Werror -Wmissing-prototypes -pedantic -x c -std=c99 -E -I. -o $@ $<

%.gen.maude: %.pre.gen.c $(PARSER)
	@$(PARSER) $(CIL_FLAGS) --out $@ $<
#tail $@
		
clean:
	rm -f *.prepre.gen.c *.pre.gen.c *.gen.maude
