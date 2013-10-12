all :
distclean : clean
	rm coq_makefile.mk

.PHONY : all distclean

FILES=proofsystem.v reduction.v generic_soundness.v generic_all.v generic_ex.v
coq_makefile.mk : Makefile
	coq_makefile ${FILES} -R . '' -install none > $@

include coq_makefile.mk
