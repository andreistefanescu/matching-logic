C_DIR = programs
SEMANTICS_DIR = semantics
PARSER_DIR = parser
SEMANTICS = match 
# match or dynamic semantics
VPATH = programs



.PHONY: all clean run test force

all: cparser maude-fragments 

dynamic: SEMANTICS=dynamic
dynamic: build-all

match: SEMANTICS=match build-all
match: build-all

force: ;

cparser: force
	make -C $(PARSER_DIR)

maude-fragments: force
	make -C $(C_DIR)

build-all: $(C_DIR)/*.gen.maude
	make -C $(SEMANTICS_DIR) $(SEMANTICS) INPUT="$(realpath $^)"
		
run: 
	maude $(SEMANTICS_DIR)/test.maude
		
clean:
	make -C $(C_DIR) clean
	make -C $(PARSER_DIR) clean
	make -C $(SEMANTICS_DIR) clean
