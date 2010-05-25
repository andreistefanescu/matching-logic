C_DIR = programs
SEMANTICS_DIR = semantics
PARSER_DIR = parser
SEMANTICS = match 
# match or dynamic semantics
VPATH = programs

.PHONY: all clean run test force cparser maude-fragments build-all dynamic match fix kcompile gcc-output kcompile-bench benchmark

all: cparser maude-fragments

dist: SEMANTICS=dynamic
dist: kcompile

dynamic: SEMANTICS=dynamic-test
dynamic: build-all run

match: SEMANTICS=match-test
match: build-all run

fix: 
	maude $(SEMANTICS_DIR)/programs-gen.maude
fixnew: 
	maude $(SEMANTICS_DIR)/kcompile_in.maude

force: ;

cparser:
	@make -C $(PARSER_DIR)

maude-fragments: cparser
	@make -C $(C_DIR)

gcc-output:
	@make -C $(C_DIR) gcc-output

kcompile: $(C_DIR)/*.gen.maude
	@time (make -C $(SEMANTICS_DIR) $(SEMANTICS) INPUT="$(realpath $^)")
	
build-all: maude-fragments kcompile

benchmark: profile.csv

profile.csv: profile.log
	perl analyzeProfile.pl > profile.csv

profile.log: SEMANTICS=dynamic
profile.log: maude-fragments kcompile-bench
	@time (maude -no-wrap $(SEMANTICS_DIR)/test-benchmark.maude > profile.log)
		
run: 
	@maude -no-wrap $(SEMANTICS_DIR)/test.maude
		
clean:
	make -C $(C_DIR) clean
	make -C $(PARSER_DIR) clean
	make -C $(SEMANTICS_DIR) clean
