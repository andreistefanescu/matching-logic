ML_ROOT_DIR=.

LIB_DIR=$(ML_ROOT_DIR)/lib
PARSER_DIR=$(ML_ROOT_DIR)/parser
SEMANTICS_DIR=$(ML_ROOT_DIR)/semantics
VIEWER_DIR=$(ML_ROOT_DIR)/viewer
DIST_DIR=$(ML_ROOT_DIR)/dist/
MATCHC_DIST_DIR=$(DIST_DIR)/matchC

PARSER_JAR=$(PARSER_DIR)/matchCparser.jar
COMPILED_FILE=matchC-compiled.maude
SEMANTICS_COMPILED_FILE=$(SEMANTICS_DIR)/$(COMPILED_FILE)
RELEASE_COMPILED_FILE=$(LIB_DIR)/$(COMPILED_FILE)
VIEWER_JAR=$(VIEWER_DIR)/matchCviewer.jar

K_BASE=/home/grosu/stefane1/k-release
K_MAUDE_LIB=$(K_BASE)/core/maude/lib

all: install

build:
	$(MAKE) -C $(PARSER_DIR)
	$(MAKE) -C $(SEMANTICS_DIR)
	$(MAKE) -C $(VIEWER_DIR)

install: build
	cp $(PARSER_JAR) $(LIB_DIR)
	cp $(SEMANTICS_COMPILED_FILE) $(LIB_DIR)
	sed -i -e 's/^load .*$$//' $(RELEASE_COMPILED_FILE)
	cp $(VIEWER_JAR) $(LIB_DIR)

dist: build
	rm -rf $(MATCHC_DIST_DIR)
	mkdir -p $(MATCHC_DIST_DIR)
	svn export bin $(MATCHC_DIST_DIR)/bin
	svn export lib $(MATCHC_DIST_DIR)/lib
	rm -rf $(MATCHC_DIST_DIR)/bin/__pycache__
	rm -rf $(MATCHC_DIST_DIR)/bin/primitive_style.yml
	rm -rf fol.k
	cp $(K_MAUDE_LIB)/k-prelude.maude $(K_MAUDE_LIB)/pl-builtins.maude \
          $(MATCHC_DIST_DIR)/lib
	cp lib/ml-prelude.maude $(MATCHC_DIST_DIR)/lib
	sed -i -e '1s/^.*$$/load k-prelude.maude/' \
          $(MATCHC_DIST_DIR)/lib/ml-prelude.maude
	svn export demo $(DIST_DIR)/demo
	cd $(DIST_DIR)
	tar cvfz matchC.tar.gz matchC
	cd $(ML_ROOT_DIR)

clean:
	$(MAKE) -C $(PARSER_DIR) clean
	$(MAKE) -C $(SEMANTICS_DIR) clean
	$(MAKE) -C $(VIEWER_DIR) clean
	rm -rf $(DIST_DIR)

