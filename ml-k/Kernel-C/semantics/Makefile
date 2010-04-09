K-MAUDE-BASE = ../../../../../k-framework/k-maude/trunk
K-COMPILE = tools/kcompile.sh
K-MAUDE = $(K-MAUDE-BASE)/$(K-COMPILE)

all: check-input semantics

check-input: 
ifeq ($(INPUT),)
	exit 1
endif

kernel-c.maude: c-maude.template $(INPUT)
	printf "`cat c-maude.template`" "including MATCH-KERNEL-C-SYNTAX ." "`cat $(INPUT)`" > kernel-c.maude
	
kernel-c-compiled.maude: kernel-c-syntax.maude kernel-c-semantics.maude kernel-c.maude fake
	$(K-MAUDE) kernel-c.maude KERNEL-C
	
semantics: kernel-c-compiled.maude

fake:

clean:
	rm -f kernel-c-compiled.maude kernel-c.maude
