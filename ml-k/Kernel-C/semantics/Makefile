K-MAUDE-BASE = ../../../../../k-framework/trunk
K-COMPILE = tools/kcompile.sh

K-MAUDE = $(K-MAUDE-BASE)/$(K-COMPILE)
K-PRELUDE = $(K-MAUDE-BASE)/k-prelude

ADDITIONAL_SYNTAX = "including MATCH-KERNEL-C-SYNTAX ."


.PHONY: all clean force check-input dynamic match

.SECONDARY:

all: dynamic 

#benchmark: $(addsuffix .gen.maude,$(TEST_PROGRAMS))

check-input: 
ifeq ($(INPUT),)
	exit 1
endif

programs-gen.maude: programs-gen.template check-input Makefile
	@printf "`cat programs-gen.template`" $(ADDITIONAL_SYNTAX) > programs-gen.maude
	for i in $(INPUT); do cat $$i >> programs-gen.maude; done
	echo endm >> programs-gen.maude
	
#"`cat $(INPUT)`" $(SEMANTICS_FILE) $(SEMANTICS_MODULE) > kernel-c.maude

kernel-c.maude: programs-gen.maude check-input c-maude.template Makefile
	printf "`cat c-maude.template`" $(K-PRELUDE) $(SEMANTICS_FILE) $(SEMANTICS_MODULE) > kernel-c.maude
	
kernel-c-compiled.maude: kernel-c.maude kernel-c-syntax.maude match-kernel-c-syntax.maude kernel-c-configuration.maude kernel-c-semantics.maude  
	$(K-MAUDE) kernel-c.maude KERNEL-C
	
dynamic: SEMANTICS_MODULE = "DYNAMIC-KERNEL-C-SEMANTICS" 
dynamic: SEMANTICS_FILE = "dynamic-kernel-c-semantics"
dynamic: semantics

match: SEMANTICS_MODULE = "MATCH-KERNEL-C-SEMANTICS"
match: SEMANTICS_FILE = "match-kernel-c-semantics"
match: semantics

semantics: kernel-c-compiled.maude test.maude

test.maude: force
	#echo $(PROGRAMS)
	@printf "`cat test.template`" "`echo -e "$(foreach var,$(INPUT), rew eval(\\"program-$(notdir $(var))\\"(.List{K})) . \n)\n"`" > test.maude

clean:
	rm -f kernel-c-compiled.maude kernel-c.maude

force: ;