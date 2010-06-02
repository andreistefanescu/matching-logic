KCC ?= ../dist/compile.sh
GCC ?= gcc -lm -Wall -Wextra -Wmissing-prototypes -pedantic -x c -std=c99
#-Werror 
PARSER ?= ../dist/cparser

DONT_RUN = goto resizeArray testStdarg testPrintf testStructInitializer twoFile1 twoFile2 \
	fix-fft getchar sumn
FAST_TESTS = quine2
CURRENT_TESTS = hexNums

# gcc -c twoFile1.c 
# gcc -c twoFile2.c 
# gcc -o a.out twoFile1.o twoFile2.o 


ALL_FILES = $(wildcard *.c)
ALL_PROGRAMS_BASIC = $(basename $(ALL_FILES))
ALL_PROGRAMS = $(filter-out $(DONT_RUN), $(ALL_PROGRAMS_BASIC))
FAST_PROGRAMS = $(filter $(FAST_TESTS), $(ALL_PROGRAMS))
CURRENT_PROGRAMS = $(filter $(CURRENT_TESTS), $(ALL_PROGRAMS_BASIC))
ALL_TARGETS = $(foreach var, $(ALL_PROGRAMS), compare-$(var).pass)
FAST_TARGETS = $(foreach var, $(FAST_PROGRAMS), compare-$(var).pass)
CURRENT_TARGETS = $(foreach var, $(CURRENT_PROGRAMS), work-run-$(var))

#.SECONDARY:

#.DELETE_ON_ERROR:

.PHONY: all test clean prepare fast-test working

test: prepare $(ALL_TARGETS)

fast-test: prepare $(FAST_TARGETS)

working: prepare $(CURRENT_TARGETS)
	
prepare:
	@rm -f information.log
	
fix:
	maude kcompile_in.maude
	
test-%:	compare-%.pass

work-compile-%.kcc: %.c $(KCC) $(PARSER)
	@echo "Running kcc..." >> information.log
	@$(KCC) -d -o $@ $<
	
work-run-%: work-compile-%.kcc
	@echo "Running $*..."
	@DEBUG=1 ./work-compile-$*.kcc 

test-%.kcc: %.c $(KCC) $(PARSER)
	@echo "Running kcc..." >> information.log
	@$(KCC) -o $@ $<
	
test-%.gcc: %.c
	@echo "Running gcc..." >> information.log
	@$(GCC) -o $@ $< 2>> information.log
	
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
	rm -f *.gcc *.kcc *.tmp compare-*.pass information.log compilation.log *-gen.maude *.pre.gen *.prepre.gen *.gen.maude a.out kcompile_* program-*-compiled.maude
