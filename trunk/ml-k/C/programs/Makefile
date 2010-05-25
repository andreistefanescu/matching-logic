PARSER_DIR = ../parser
PARSER = $(PARSER_DIR)/cparser

ALL_FILES = $(wildcard *.c)
ALL_PROGRAMS = $(basename $(ALL_FILES))
CIL_FLAGS = --noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused 
PEDANTRY_OPTIONS=-Wall -Wextra -Werror -Wmissing-prototypes -pedantic -x c -std=c99
GCC_OPTIONS=-nostdlib -nodefaultlibs

#.SECONDARY:

.PHONY: all clean benchmark

all: $(addsuffix .gen.maude,$(ALL_PROGRAMS))

%.prepre.gen: %.c embed.pl Makefile fsl.h printf.h
	@perl embed.pl -d=ML -o=$@ $<

%.pre.gen: %.prepre.gen
	@gcc $(PEDANTRY_OPTIONS) -E -I. -o $@ $<

%.gen.maude: %.pre.gen $(PARSER)
	@$(PARSER) $(CIL_FLAGS) --out $@.tmp $<
	@mv $@.tmp $@
		
clean:
	rm -f *.prepre.gen *.pre.gen *.gen.maude *.gcc *.tmp
