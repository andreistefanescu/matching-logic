.PHONY: build test

PROGRAMS = $(wildcard programs/*/*.k)
TEST_RESULTS = ${PROGRAMS:.k=.out}

build: wcet-original-compiled.maude

test: ${TEST_RESULTS}

%.out: %.r %-compiled.maude
	./wcet-prover $*

%-compiled.maude: %.k wcet.k lib/matching-logic.k lib/naive-domain-reasoning.k wcet-domain-reasoning.k
	kompile $< -addTopCell -transition computational

wcet-original-compiled.maude: wcet-original.k
	kompile wcet-original.k -l WCET
