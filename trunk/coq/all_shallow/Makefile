all :
distclean : clean
	rm coq_makefile.mk

.PHONY : all distclean

coq_makefile.mk :
	coq_makefile proofsystem.v soundness.v > $@

include coq_makefile.mk
