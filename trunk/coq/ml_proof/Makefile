all :
distclean : clean
	rm coq_makefile.mk

.PHONY : all distclean

coq_makefile.mk :
	coq_makefile matchinglpartialcorrectness.v  reduction.v matchinglreduction.v matchinglproofsystem.v matchingl.v generic.v > $@

include coq_makefile.mk
