all :
distclean : clean
	rm coq_makefile.mk

.PHONY : all distclean

FILES=proofsystem.v soundness.v example.v dekker.v
coq_makefile.mk : Makefile
	coq_makefile ${FILES} -R ../ml_proof '' -install none > $@

include coq_makefile.mk
