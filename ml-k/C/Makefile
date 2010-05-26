C_DIR = programs
SEMANTICS_DIR = semantics
PARSER_DIR = parser
SEMANTICS = match 
DIST_DIR = dist
# match or dynamic semantics
VPATH = programs

.PHONY: all clean run test force cparser maude-fragments build-all dynamic match fix kcompile gcc-output kcompile-bench benchmark dist

all: cparser maude-fragments

dist: SEMANTICS=dynamic
dist: cparser kcompile
	@mkdir -p $(DIST_DIR)
	@echo | cat $(SEMANTICS_DIR)/c-compiled.maude $(SEMANTICS_DIR)/c-syntax.maude - $(SEMANTICS_DIR)/common-c-configuration.maude | perl $(SEMANTICS_DIR)/slurp.pl $(SEMANTICS_DIR)/ > $(DIST_DIR)/c-compiled.maude
	@cp $(SEMANTICS_DIR)/compile.sh $(DIST_DIR)
#@ln -s $(DIST_DIR)/compile.sh $(DIST_DIR)/kcc
	@cp $(SEMANTICS_DIR)/slurp.pl $(DIST_DIR)
	@cp $(SEMANTICS_DIR)/wrapper.pl $(DIST_DIR)
	@cp $(PARSER_DIR)/cparser $(DIST_DIR)
	@cp $(C_DIR)/compileProgram.sh $(DIST_DIR)
	@cp $(C_DIR)/embed.pl $(DIST_DIR)
	@cp $(C_DIR)/fsl.h $(DIST_DIR)
	@cp $(C_DIR)/stdio.h $(DIST_DIR)
	@cp $(C_DIR)/stdlib.h $(DIST_DIR)
	@cp $(C_DIR)/math.h $(DIST_DIR)
	@cp $(C_DIR)/string.h $(DIST_DIR)
	@cp $(C_DIR)/stdarg.h $(DIST_DIR)
	@cp $(C_DIR)/stddef.h $(DIST_DIR)
	@cp $(C_DIR)/stdint.h $(DIST_DIR)

test: dist
	@make -C $(C_DIR) test
	

# match: SEMANTICS=match-test
# match: build-all run

fix: 
	maude $(SEMANTICS_DIR)/programs-gen.maude
fixnew: 
	maude $(SEMANTICS_DIR)/kcompile_in.maude

force: ;

cparser:
	@make -C $(PARSER_DIR)

kcompile:
	@make -C $(SEMANTICS_DIR) $(SEMANTICS)
	
# build-all: maude-fragments kcompile
# @time (make -C $(SEMANTICS_DIR) $(SEMANTICS) INPUT="$(realpath $^)")

benchmark: profile.csv

profile.csv: profile.log
	perl analyzeProfile.pl > profile.csv

# profile.log: SEMANTICS=dynamic
# profile.log: maude-fragments kcompile-bench
	# @time (maude -no-wrap $(SEMANTICS_DIR)/test-benchmark.maude > profile.log)
		
# run: 
	# @maude -no-wrap $(SEMANTICS_DIR)/test.maude
		
clean:
	make -C $(C_DIR) clean
	make -C $(PARSER_DIR) clean
	make -C $(SEMANTICS_DIR) clean
	rm -rf $(DIST_DIR)
