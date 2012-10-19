include coq_makefile.mk

all :
clean :
distclean : clean
	rm coq_makefile.mk
.PHONY : all clean distclean


FILES=domains.v kstyle.v

coq_makefile.mk : Makefile
	coq_makefile ${FILES} -install none -o tmp.mk -R ../../ml_proof '' && mv tmp.mk $@ 
