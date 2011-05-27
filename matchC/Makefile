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

K_BASE=/home/grosu/grosu/k-framework
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

dist: install
	rm -rf $(MATCHC_DIST_DIR)
	mkdir -p $(MATCHC_DIST_DIR)
	cp LICENSE $(MATCHC_DIST_DIR)
	cp README $(MATCHC_DIST_DIR)
	svn export bin $(MATCHC_DIST_DIR)/bin
	svn export lib $(MATCHC_DIST_DIR)/lib
	svn export demo $(MATCHC_DIST_DIR)/demo
	mv $(MATCHC_DIST_DIR)/bin/matchC.py $(MATCHC_DIST_DIR)/bin/matchC
	rm -rf $(MATCHC_DIST_DIR)/bin/__pycache__
	rm -rf $(MATCHC_DIST_DIR)/bin/primitive_style.yml
	rm -rf $(MATCHC_DIST_DIR)/lib/fol.k
	cp $(K_MAUDE_LIB)/k-prelude.maude $(K_MAUDE_LIB)/pl-builtins.maude \
          $(MATCHC_DIST_DIR)/lib
	cp lib/ml-prelude.maude $(MATCHC_DIST_DIR)/lib
	sed -i -e '1s/^load.*k-prelude.maude$$/load k-prelude.maude/' \
          $(MATCHC_DIST_DIR)/lib/ml-prelude.maude
	tar cvfz $(DIST_DIR)/matchC.tar.gz $(MATCHC_DIST_DIR)

clean:
	$(MAKE) -C $(PARSER_DIR) clean
	$(MAKE) -C $(SEMANTICS_DIR) clean
	$(MAKE) -C $(VIEWER_DIR) clean
	rm -rf $(DIST_DIR)

