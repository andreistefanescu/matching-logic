PARSER_DIR = ../parser
PARSER = $(PARSER_DIR)/cparser
TEST_PROGRAMS = multWithBreak simplest sumn factorial hard listReverse

ALL_FILES = $(wildcard *.c)
ALL_PROGRAMS = $(basename $(ALL_FILES))
CIL_FLAGS = --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused 
PEDANTRY_OPTIONS=-Wall -Wextra -Werror -Wmissing-prototypes -pedantic -x c -std=c99

#.SECONDARY:

.PHONY: all clean benchmark

all: $(addsuffix .gen.maude,$(ALL_PROGRAMS))

benchmark: $(addsuffix .gen.maude,$(TEST_PROGRAMS))

%.prepre.gen: %.c embed.pl Makefile
	@perl embed.pl -d=ML -o=$@ $<

%.pre.gen: %.prepre.gen
	@gcc $(PEDANTRY_OPTIONS) -E -I. -o $@ $<

%.gen.maude: %.pre.gen $(PARSER)
	@$(PARSER) $(CIL_FLAGS) --out $@ $<
#tail $@

gcc-output: $(addsuffix .gcc,$(ALL_PROGRAMS))
	echo $(PIPESTATUS)

%.gcc: %.c
	gcc $(PEDANTRY_OPTIONS) -o $@ $<
		
clean:
	rm -f *.prepre.gen *.pre.gen *.gen.maude *.gcc
