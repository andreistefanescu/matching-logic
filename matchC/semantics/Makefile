LANG_NAME = kernelC
EXT_NAME = matchC

KC = kompile

ML_ROOT_DIR = ..
ML_LIB_DIR = $(ML_ROOT_DIR)/lib
ML_PATTERNS_DIR = $(ML_ROOT_DIR)/patterns
ML_PRELUDE = $(ML_LIB_DIR)/ml-prelude.maude

LANG_K_SYNTAX = $(LANG_NAME)-syntax.k
LANG_K_SEMANTICS = $(LANG_NAME)-semantics.k
LANG_K_MAIN = $(LANG_NAME).k
LANG_K_FILES = $(LANG_K_SYNTAX) $(LANG_K_SEMANTICS) $(LANG_K_MAIN)
LANG_COMPILED = $(LANG_NAME)-compiled.maude

EXT_K_SYNTAX = $(EXT_NAME)-syntax.k
EXT_K_SEMANTICS = $(EXT_NAME)-semantics.k
EXT_K_MAIN = $(EXT_NAME).k
EXT_K_FOL = $(ML_LIB_DIR)/fol.k
EXT_K_IO = $(ML_PATTERNS_DIR)/io.k
EXT_K_STACK = $(ML_PATTERNS_DIR)/stack.k
EXT_K_LIST = $(ML_PATTERNS_DIR)/list.k
EXT_K_BINARY_TREE = $(ML_PATTERNS_DIR)/binary_tree.k
EXT_K_BINARY_HEIGHT_TREE = $(ML_PATTERNS_DIR)/binary_height_tree.k
EXT_K_FILES = $(LANG_K_SYNTAX) $(LANG_K_SEMANTICS) \
              $(EXT_K_SYNTAX) $(EXT_K_SEMANTICS) \
              $(EXT_K_FOL) \
              $(EXT_K_IO) $(EXT_K_STACK) $(EXT_K_LIST) \
							$(EXT_K_BINARY_TREE) $(EXT_K_BINARY_HEIGHT_TREE) \
              $(EXT_K_MAIN)
EXT_COMPILED = $(EXT_NAME)-compiled.maude

CLEAN_FILES = $(LANG_COMPILED) \
              $(LANG_COMPILED)-e \
              $(LANG_K_FILES:.k=.maude) \
              $(EXT_COMPILED) \
              $(EXT_COMPILED)-e \
              $(EXT_K_FILES:.k=.maude) \
              shared.maude


all: build

build: $(EXT_COMPILED)


$(EXT_COMPILED) : $(EXT_K_FILES) 
	$(KC) -prelude $(ML_PRELUDE) $(EXT_NAME)

$(LANG_COMPILED): $(LANG_K_FILES)
	$(KC) -prelude $(ML_PRELUDE) $(LANG_NAME)


clean:
	rm -f $(CLEAN_FILES) kompile_* *~

