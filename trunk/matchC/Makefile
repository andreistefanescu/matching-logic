ML_ROOT_DIR=.

LIB_DIR=$(ML_ROOT_DIR)/lib
PARSER_DIR=$(ML_ROOT_DIR)/parser
SEMANTICS_DIR=$(ML_ROOT_DIR)/semantics
VIEWER_DIR=$(ML_ROOT_DIR)/viewer
DIST_DIR=$(ML_ROOT_DIR)/dist
MATCHC_DIST_DIR=$(DIST_DIR)/matchC

LOCAL_HOST_NAME=`hostname`
FSL_HOST_NAME='fsl3.cs.uiuc.edu'
FSL_SOFTWARE_DIR=/home/software
FSL_MATCHC_DIR=$(FSL_SOFTWARE_DIR)/matchC

PARSER_JAR=$(PARSER_DIR)/matchCparser.jar
COMPILED_FILE=matchC-compiled.maude
SEMANTICS_COMPILED_FILE=$(SEMANTICS_DIR)/$(COMPILED_FILE)
RELEASE_COMPILED_FILE=$(LIB_DIR)/$(COMPILED_FILE)
VIEWER_JAR=$(VIEWER_DIR)/matchCviewer.jar

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

dist:
	rm -rf $(MATCHC_DIST_DIR)
	mkdir -p $(MATCHC_DIST_DIR)
	cp LICENSE $(MATCHC_DIST_DIR)
	cp README $(MATCHC_DIST_DIR)
	svn export bin $(MATCHC_DIST_DIR)/bin
	svn export lib $(MATCHC_DIST_DIR)/lib
	svn export demo $(MATCHC_DIST_DIR)/demo
	svn export examples $(MATCHC_DIST_DIR)/examples
	mv $(MATCHC_DIST_DIR)/bin/matchC.py $(MATCHC_DIST_DIR)/bin/matchC
	rm -rf $(MATCHC_DIST_DIR)/bin/__pycache__
	rm -rf $(MATCHC_DIST_DIR)/bin/primitive_style.yml
	rm -rf $(MATCHC_DIST_DIR)/lib/fol.k
	cp $(K_MAUDE_LIB)/k-prelude.maude $(K_MAUDE_LIB)/pl-builtins.maude \
    $(K_MAUDE_LIB)/socket.maude $(MATCHC_DIST_DIR)/lib
	cp lib/ml-prelude.maude $(MATCHC_DIST_DIR)/lib
	sed -i -e '1s/^load.*k-prelude.maude$$/load k-prelude.maude/' \
    $(MATCHC_DIST_DIR)/lib/ml-prelude.maude

pack: install dist
	bash -c 'cd $(DIST_DIR); tar cvfz matchC.tar.gz matchC'

online: dist
	if [ $(LOCAL_HOST_NAME) = $(FSL_HOST_NAME) ]; \
  then \
    rm -rf $(FSL_MATCHC_DIR); \
    cp -r $(MATCHC_DIST_DIR) $(FSL_SOFTWARE_DIR); \
    mkdir $(FSL_MATCHC_DIR)/online; \
    mv $(FSL_MATCHC_DIR)/demo $(FSL_MATCHC_DIR)/online/DEMO; \
    mv $(FSL_MATCHC_DIR)/examples/* $(FSL_MATCHC_DIR)/online/; \
    chmod -R 777 $(FSL_MATCHC_DIR); \
  fi

clean:
	$(MAKE) -C $(PARSER_DIR) clean
	$(MAKE) -C $(SEMANTICS_DIR) clean
	$(MAKE) -C $(VIEWER_DIR) clean
	rm -rf $(DIST_DIR)

