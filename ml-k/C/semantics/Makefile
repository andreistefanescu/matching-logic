K-MAUDE-BASE = ../../../../../k-framework/trunk
K-COMPILE-BASE = tools/kcompileFast.sh
K-PROGRAM-COMPILE = $(K-MAUDE-BASE)/tools/kcompile-program.sh

K-MAUDE = $(K-MAUDE-BASE)/$(K-COMPILE-BASE)
K-PRELUDE = $(K-MAUDE-BASE)/k-prelude

ADDITIONAL_SYNTAX = "including MATCH-C-SYNTAX ."

PROGRAM_BASE_NAMES = $(foreach var,$(INPUT), $(notdir $(subst .gen.maude,,$(var))))
PROGRAM_NAMES = $(foreach var, $(PROGRAM_BASE_NAMES), program-$(var))
PROGRAM_DIR = ../programs
PROGRAM_TARGET = $(foreach var, $(PROGRAM_BASE_NAMES), program-$(var)-compiled.maude)
PROGRAM_TARGET_NO_MAUDE = $(foreach var, $(PROGRAM_BASE_NAMES), program-$(var)-compiled)
COMPILED_PROGRAM_LOADS = `echo -e "$(foreach var, $(PROGRAM_TARGET_NO_MAUDE), load $(var) .\n)"`


.PHONY: all clean force check-input dynamic match semantics

#.SECONDARY:

all: dynamic 

check-input: 
ifeq ($(INPUT),)
	exit 1
endif

programs-gen.maude: c-syntax.maude programs-gen.template $(INPUT) Makefile
ifeq ($(INPUT),)
	exit 1
endif
	@printf "`cat programs-gen.template`" $(ADDITIONAL_SYNTAX) > programs-gen.maude
	@for i in $(INPUT); do cat $$i >> programs-gen.maude; done
	@echo endm >> programs-gen.maude
	
c-syntax.maude: Makefile
	@printf "`cat c-syntax.template`" $(ADDITIONAL_SYNTAX) > c-syntax.maude	
	
c.maude: c-syntax.maude programs-gen.maude c-maude.template Makefile
ifeq ($(INPUT),)
	exit 1
endif
	@printf "`cat c-maude.template`" $(K-PRELUDE) $(CONFIGURATION_FILE) $(SEMANTICS_FILE) $(SEMANTICS_MODULE) > c.maude
	
c-compiled.maude: c.maude common-c-syntax.maude match-c-syntax.maude common-c-configuration.maude common-c-semantics.maude  
	$(K-MAUDE) c.maude C
	
program-%-compiled.maude: c-compiled.maude programs-gen.maude
	$(K-PROGRAM-COMPILE) programs-gen.maude C C-PROGRAM program-$*
	sed '1 d' $@ > $@.tmp
	mv $@.tmp $@
	
dynamic: SEMANTICS_MODULE = "DYNAMIC-C-SEMANTICS" 
dynamic: SEMANTICS_FILE = "dynamic-c-semantics"
dynamic: CONFIGURATION_FILE = "dynamic-c-configuration"
dynamic: semantics

match: SEMANTICS_MODULE = "MATCH-C-SEMANTICS"
match: SEMANTICS_FILE = "match-c-semantics"
match: CONFIGURATION_FILE = "match-c-configuration"
match: semantics

semantics: c-compiled.maude test.maude

test.maude: $(PROGRAM_TARGET)
	@printf "`cat test.template`" "$(COMPILED_PROGRAM_LOADS)" "`echo -e "$(foreach var, $(PROGRAM_NAMES), rew in C-$(var) : eval(\\"$(var)\\"(.List{K})) . \n)\n"`" > test.maude
	
clean:
	rm -f program-*-compiled.maude program-*-compiled.maude.tmp c-syntax.maude c-compiled.maude c.maude test.maude programs-gen.maude test-benchmark.maude kcompile_*

force: ;
