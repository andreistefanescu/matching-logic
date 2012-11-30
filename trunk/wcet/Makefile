.PHONY: build

PROGRAMS = $(wildcard programs/*/*.k)
TEST_RESULTS = ${PROGRAMS:.k=.out}

build: ${TEST_RESULTS}

%.out: %.r %-compiled.maude
	./wcet-prover $< --compiled-def	$*-compiled.maude

%-compiled.maude: %.k
	kompile $< -addTopCell -transition computational
