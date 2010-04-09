K-MAUDE-BASE = ../../../../../k-framework/k-maude/trunk
K-COMPILE = tools/kcompile.sh

K-MAUDE = $(K-MAUDE-BASE)/$(K-COMPILE)
K-PRELUDE = $(K-MAUDE-BASE)/k-prelude

ADDITIONAL_SYNTAX = "including MATCH-KERNEL-C-SYNTAX ."

.PHONY: all clean

all: dynamic

check-input: 
ifeq ($(INPUT),)
	exit 1
endif

kernel-c.maude: check-input c-maude.template $(INPUT) Makefile
	printf "`cat c-maude.template`" $(K-PRELUDE) $(ADDITIONAL_SYNTAX) "`cat $(INPUT)`" $(SEMANTICS_FILE) $(SEMANTICS_MODULE) > kernel-c.maude
	
kernel-c-compiled.maude: kernel-c.maude kernel-c-syntax.maude match-kernel-c-syntax.maude kernel-c-configuration.maude kernel-c-semantics.maude  
	$(K-MAUDE) kernel-c.maude KERNEL-C
	
dynamic: SEMANTICS_MODULE = "DYNAMIC-KERNEL-C-SEMANTICS" 
dynamic: SEMANTICS_FILE = "dynamic-kernel-c-semantics"
dynamic: semantics

match: SEMANTICS_MODULE = "MATCH-KERNEL-C-SEMANTICS"
match: SEMANTICS_FILE = "match-kernel-c-semantics"
match: semantics

semantics: kernel-c-compiled.maude

clean:
	rm -f kernel-c-compiled.maude kernel-c.maude
