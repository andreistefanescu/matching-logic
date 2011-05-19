ML_ROOT_DIR=.

LIB_DIR=$(ML_ROOT_DIR)/lib
PARSER_DIR=$(ML_ROOT_DIR)/parser
SEMANTICS_DIR=$(ML_ROOT_DIR)/semantics
VIEWER_DIR=$(ML_ROOT_DIR)/viewer
DIST_ROOT_DIR=$(ML_ROOT_DIR)/dist/
DIST_DIR=$(DIST_ROOT_DIR)/matchC

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
	rm -rf $(DIST_DIR)
	mkdir -p $(DIST_DIR)
	svn export bin $(DIST_DIR)/bin
	svn export lib $(DIST_DIR)/lib
	rm -rf $(DIST_DIR)/lib/__pycache__
	cp $(K_MAUDE_LIB)/k-prelude.maude $(K_MAUDE_LIB)/pl-builtins.maude \
          $(DIST_DIR)/lib
	cp lib/ml-prelude.maude $(DIST_DIR)/lib
	sed -i -e '1s/^.*$$/load k-prelude.maude/' \
          $(DIST_DIR)/lib/ml-prelude.maude
	svn export demo $(DIST_DIR)/demo
	cd $(DIST_ROOT_DIR)
	tar cvfz matchC.tar.gz matchC
	cd $(ML_ROOT_DIR)

clean:
	$(MAKE) -C $(PARSER_DIR) clean
	$(MAKE) -C $(SEMANTICS_DIR) clean
	$(MAKE) -C $(VIEWER_DIR) clean
	rm -rf $(DIST_DIR)

