
.PHONY: all default test test-gcc clean

all: test

default: 

test: default
	runtest --tool=gcc gcc.tiny/tiny.exp --tool_exec "kcc -d"

test-gcc: default
	runtest --tool=gcc gcc.tiny/tiny.exp --tool_exec "gcc --std=c99"

clean:
	rm -f kcompile_* compilation.log gcc.log gcc.sum *.pre.gen a.out *.maude.tmp *-gen.maude *.prepre.gen *.gen.maude *-compiled.maude *.warnings.log