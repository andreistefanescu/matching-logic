include coq_makefile.mk

all :
extract : a.out
clean : extractclean
distclean : clean
	rm -f coq_makefile.mk a.out
extractclean :
	rm -f eval.ml eval.mli *.cmi *.cmo *.cmx *.o
	rm -f extraction.vo extraction.glob extraction.v.d
.PHONY : all extract clean extractclean distclean

FILES=domains.v kstyle.v evaluator.v simple_proofs.v

coq_makefile.mk : Makefile
	coq_makefile ${FILES} -install none -o tmp.mk -R ../../ml_proof '' && mv tmp.mk $@ 

eval.ml eval.mli : evaluator.vo extraction.v kstyle.vo
	coqc extraction.v
eval.cmi : eval.mli
	ocamlc eval.mli

eval.cmx : eval.ml eval.cmi
	ocamlopt -c eval.ml

a.out : eval.cmx run.ml
	ocamlopt eval.cmx run.ml
