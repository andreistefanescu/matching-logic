C_DIR = programs
SEMANTICS_DIR = semantics
PARSER_DIR = parser
SEMANTICS = match 
# match or dynamic semantics
VPATH = programs



.PHONY: all clean run test force cparser maude-fragments build-all dynamic match

all: cparser maude-fragments 

dynamic: SEMANTICS=dynamic
dynamic: build-all run

match: SEMANTICS=match build-all
match: build-all run

force: ;

cparser:
	@make -C $(PARSER_DIR)

maude-fragments: cparser
	@make -C $(C_DIR)

build-all: maude-fragments $(C_DIR)/*.gen.maude
	@make -C $(SEMANTICS_DIR) $(SEMANTICS) INPUT="$(realpath $^)"
		
run: 
	@maude $(SEMANTICS_DIR)/test.maude
		
clean:
	make -C $(C_DIR) clean
	make -C $(PARSER_DIR) clean
	make -C $(SEMANTICS_DIR) clean
