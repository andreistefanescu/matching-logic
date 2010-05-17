K-MAUDE-BASE = ../../../../../k-framework/trunk
K-COMPILE-BASE = tools/kcompile.sh
K-PROGRAM-COMPILE = $(K-MAUDE-BASE)/tools/kcompile-program.sh

K-MAUDE = $(K-MAUDE-BASE)/$(K-COMPILE-BASE)
K-PRELUDE = $(K-MAUDE-BASE)/k-prelude

ADDITIONAL_SYNTAX = "including MATCH-C-SYNTAX ."

PROGRAM_BASE_NAMES = $(foreach var,$(INPUT), $(notdir $(var)))
PROGRAM_NAMES = $(foreach var, $(PROGRAM_BASE_NAMES), program-$(var))
PROGRAM_DIR = ../programs
PROGRAM_TARGET = $(foreach var, $(PROGRAM_BASE_NAMES), program-$(var)-compiled.maude)


.PHONY: all clean force check-input dynamic match semantics

#.SECONDARY:

all: dynamic 

#benchmark: $(addsuffix .gen.maude,$(TEST_PROGRAMS))

check-input: 
ifeq ($(INPUT),)
	exit 1
endif

programs-gen.maude: programs-gen.template $(INPUT) Makefile
ifeq ($(INPUT),)
	exit 1
endif
	@printf "`cat programs-gen.template`" $(ADDITIONAL_SYNTAX) > programs-gen.maude
	@for i in $(INPUT); do cat $$i >> programs-gen.maude; done
	@echo endm >> programs-gen.maude
	
#"`cat $(INPUT)`" $(SEMANTICS_FILE) $(SEMANTICS_MODULE) > c.maude

c.maude: programs-gen.maude c-maude.template Makefile
ifeq ($(INPUT),)
	exit 1
endif
	@printf "`cat c-maude.template`" $(K-PRELUDE) $(CONFIGURATION_FILE) $(SEMANTICS_FILE) $(SEMANTICS_MODULE) > c.maude
	
c-compiled.maude: force c.maude common-c-syntax.maude match-c-syntax.maude common-c-configuration.maude common-c-semantics.maude  
#echo $(PROGRAM_NAMES)
	$(K-MAUDE) c.maude C
	
dynamic: SEMANTICS_MODULE = "DYNAMIC-C-SEMANTICS" 
dynamic: SEMANTICS_FILE = "dynamic-c-semantics"
dynamic: CONFIGURATION_FILE = "dynamic-c-configuration"
dynamic: semantics

match: SEMANTICS_MODULE = "MATCH-C-SEMANTICS"
match: SEMANTICS_FILE = "match-c-semantics"
match: CONFIGURATION_FILE = "match-c-configuration"
match: semantics

# $(PROGRAM_TARGET) 
semantics: c-compiled.maude test.maude test-benchmark.maude

#program-%-compiled.maude: $(PROGRAM_DIR)/% programs-gen.maude
#	$(K-PROGRAM-COMPILE) sepcomp.maude C C-PROGRAM program-$(notdir $<)

test.maude: force
	@printf "`cat test.template`" "`echo -e "$(foreach var, $(PROGRAM_NAMES), rew eval(\\"$(var)\\"(.List{K})) . \n)\n"`" > test.maude
	
test-benchmark.maude: force
	@printf "`cat test-benchmark.template`" "`echo -e "$(foreach var, $(PROGRAM_NAMES), rew eval(\\"$(var)\\"(.List{K})) . \n)\n"`" > test-benchmark.maude

clean:
	rm -f c-compiled.maude c.maude test.maude programs-gen.maude test-benchmark.maude kcompile_*

force: ;
