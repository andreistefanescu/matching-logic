C_DIR = programs
SEMANTICS_DIR = semantics
PARSER_DIR = parser
SEMANTICS = match 
# match or dynamic semantics
VPATH = programs

.PHONY: all clean run test force cparser maude-fragments build-all dynamic match fix kcompile gcc-output

all: cparser maude-fragments 

dynamic: SEMANTICS=dynamic
dynamic: build-all run

match: SEMANTICS=match
match: build-all run

fix: 
	maude $(SEMANTICS_DIR)/kernel-c.maude

force: ;

cparser:
	@make -C $(PARSER_DIR)

maude-fragments: cparser
	@make -C $(C_DIR)

gcc-output:
	@make -C $(C_DIR) gcc-output

kcompile: $(C_DIR)/*.gen.maude
	@make -C $(SEMANTICS_DIR) $(SEMANTICS) INPUT="$(realpath $^)"
	
build-all: maude-fragments kcompile
		
run: 
	@maude $(SEMANTICS_DIR)/test.maude
		
clean:
	make -C $(C_DIR) clean
	make -C $(PARSER_DIR) clean
	make -C $(SEMANTICS_DIR) clean
