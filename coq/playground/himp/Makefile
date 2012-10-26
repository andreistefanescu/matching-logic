include coq_makefile.mk

all :
clean :
distclean : clean
	rm coq_makefile.mk
.PHONY : all clean distclean


FILES=domains.v kstyle.v

coq_makefile.mk : Makefile
	coq_makefile ${FILES} -install none -o tmp.mk -R ../../ml_proof '' && mv tmp.mk $@ 

eval.ml eval.mli : extraction.v kstyle.vo
	coqc extraction.v
eval.cmi : eval.mli
	ocamlc eval.mli

eval.cmx : eval.ml eval.cmi
	ocamlopt -c eval.ml

a.out : eval.cmx run.ml
	ocamlopt eval.cmx run.ml
