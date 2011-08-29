ML_ROOT_DIR=.
K_BASE=/Users/andrei/k-release

LIB_DIR=$(ML_ROOT_DIR)/lib/
PARSER_DIR=$(ML_ROOT_DIR)/parser/
SEMANTICS_DIR=$(ML_ROOT_DIR)/semantics/
VIEWER_DIR=$(ML_ROOT_DIR)/viewer/
DIST_DIR=$(ML_ROOT_DIR)/dist/
MATCHC_DIST_DIR=$(DIST_DIR)/matchC/

LOCAL_HOST_NAME=`hostname`
FSL_HOST_NAME='fsl3.cs.uiuc.edu'
FSL_MATCHC_ONLINE_DIR=/www/www-root/extensions_stefane1/matchC_online/

PARSER_JAR=$(PARSER_DIR)/matchCparser.jar
COMPILED_FILE=matchC-compiled.maude
SEMANTICS_COMPILED_FILE=$(SEMANTICS_DIR)/$(COMPILED_FILE)
RELEASE_COMPILED_FILE=$(LIB_DIR)/$(COMPILED_FILE)
VIEWER_JAR=$(VIEWER_DIR)/matchCviewer.jar

K_LIB=$(K_BASE)/core/maude/lib/


.PHONY: build install dist pack online

all: install

klib:
	cp $(K_LIB)/k-prelude.maude $(LIB_DIR)
	cp $(K_LIB)/pl-builtins.maude $(LIB_DIR)
	cp $(K_LIB)/socket.maude $(LIB_DIR)

build: klib
	$(MAKE) -C $(PARSER_DIR)
	$(MAKE) -C $(SEMANTICS_DIR)
	$(MAKE) -C $(VIEWER_DIR)

install: build
	cp $(PARSER_JAR) $(LIB_DIR)
	sed '1d' $(SEMANTICS_COMPILED_FILE) >$(RELEASE_COMPILED_FILE)
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
	rm $(MATCHC_DIST_DIR)/lib/fol.k

pack: install dist
	bash -c 'cd $(DIST_DIR); tar cvfz matchC.tar.gz matchC'

online: dist
	if [ $(LOCAL_HOST_NAME) = $(FSL_HOST_NAME) ]; \
  then \
    ( \
      umask 0000; \
      rm -rf $(FSL_MATCHC_ONLINE_DIR); \
      cp -r $(MATCHC_DIST_DIR) $(FSL_MATCHC_ONLINE_DIR); \
      mv $(FSL_MATCHC_ONLINE_DIR)/demo $(FSL_MATCHC_ONLINE_DIR)/examples/DEMO; \
    ) \
  fi

clean:
	$(MAKE) -C $(PARSER_DIR) clean
	$(MAKE) -C $(SEMANTICS_DIR) clean
	$(MAKE) -C $(VIEWER_DIR) clean
	rm -rf $(DIST_DIR)

