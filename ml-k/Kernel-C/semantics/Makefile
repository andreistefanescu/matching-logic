K-MAUDE-BASE = ../../../../../k-framework/k-maude/trunk
K-COMPILE = tools/kcompile.sh
K-MAUDE = $(K-MAUDE-BASE)/$(K-COMPILE)

all: semantics

kernel-c-compiled.maude: kernel-c-syntax.maude kernel-c-semantics.maude
	$(K-MAUDE) kernel-c-semantics.maude KERNEL-C
	
semantics: kernel-c-compiled.maude

clean:
	rm -f kernel-c-compiled.maude
