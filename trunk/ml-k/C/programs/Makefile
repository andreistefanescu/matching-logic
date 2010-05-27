KCC ?= ../dist/compile.sh
GCC ?= gcc -lm -Wall -Wextra -Wmissing-prototypes -pedantic -x c -std=c99
#-Werror 
PARSER ?= ../dist/cparser

DONT_RUN = goto resizeArray testStdarg

ALL_FILES = $(wildcard *.c)
ALL_PROGRAMS_BASIC = $(basename $(ALL_FILES))
ALL_PROGRAMS = $(filter-out $(DONT_RUN), $(ALL_PROGRAMS_BASIC))
ALL_TARGETS = $(foreach var, $(ALL_PROGRAMS), compare-$(var).pass)

#.SECONDARY:

.DELETE_ON_ERROR:

.PHONY: all test clean prepare

test: prepare $(ALL_TARGETS)

prepare:
	@rm -f information.log
	
test-%:	compare-%.pass

test-%.kcc: %.c $(KCC) $(PARSER)
	@$(KCC) -o $@ $<
	
test-%.gcc: %.c
	@$(GCC) -o $@ $< 2> information.log
	
output-% retval-%: test-%
	@echo "Running $*..."
	@./test-$* > output-$*.tmp; RETURN_VALUE=$$?; echo $$RETURN_VALUE > retval-$*
	@mv output-$*.tmp output-$*
	
compare-%.pass: output-%.gcc retval-%.gcc output-%.kcc retval-%.kcc
	@echo "Comparing $*..."
	@diff -y --suppress-common-lines -I '^VOLATILE' output-$*.gcc output-$*.kcc
	@diff -y --suppress-common-lines retval-$*.gcc retval-$*.kcc
	@touch compare-$*.pass
		
clean:
	rm -f *.gcc *.kcc *.tmp compare-*.pass information.log compilation.log *-gen.maude
