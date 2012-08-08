include coq_makefile.mk

all :
clean :
distclean : clean
	rm coq_makefile.mk
.PHONY : all clean distclean

coq_makefile.mk : files Makefile
	coq_makefile -no-install -f files -o tmp.mk -R ../../ml_proof '' && mv tmp.mk $@ 
