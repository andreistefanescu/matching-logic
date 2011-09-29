ML_ROOT_DIR=.
K_BASE=/home/grosu/stefane1/k-release

LIB_DIR=$(ML_ROOT_DIR)/lib/
SEMANTICS_DIR=$(ML_ROOT_DIR)/semantics/
PARSER_DIR=$(ML_ROOT_DIR)/parser/
VIEWER_DIR=$(ML_ROOT_DIR)/viewer/
EXAMPLES_DIR=$(ML_ROOT_DIR)/examples/
DIST_DIR=$(ML_ROOT_DIR)/dist/
MATCHC_DIST_DIR=$(DIST_DIR)/matchC/

K_LIB=$(K_BASE)/core/maude/lib/

PARSER_JAR=$(PARSER_DIR)/matchCparser.jar
COMPILED_FILE=matchC-compiled.maude
SEMANTICS_COMPILED_FILE=$(SEMANTICS_DIR)/$(COMPILED_FILE)
RELEASE_COMPILED_FILE=$(LIB_DIR)/$(COMPILED_FILE)
VIEWER_JAR=$(VIEWER_DIR)/matchCviewer.jar

LOCAL_HOST_NAME=`hostname`
FSL_HOST_NAME='fsl3.cs.uiuc.edu'
FSL_MATCHC_ONLINE_DIR=/www/www-root/extensions_stefane1/matchC_online/


.PHONY: build install dist pack online test

all: install

klib:
	cp $(K_LIB)/k-prelude.maude $(LIB_DIR)
	cp $(K_LIB)/pl-builtins.maude $(LIB_DIR)
	cp $(K_LIB)/socket.maude $(LIB_DIR)

build: klib
	$(MAKE) -C $(SEMANTICS_DIR)
	$(MAKE) -C $(PARSER_DIR)
	$(MAKE) -C $(VIEWER_DIR)

install: build
	sed '1d' $(SEMANTICS_COMPILED_FILE) >$(RELEASE_COMPILED_FILE)
	cp $(PARSER_JAR) $(LIB_DIR)
	cp $(VIEWER_JAR) $(LIB_DIR)

dist:
	rm -rf $(MATCHC_DIST_DIR)
	mkdir -p $(MATCHC_DIST_DIR)
	cp LICENSE $(MATCHC_DIST_DIR)
	cp README $(MATCHC_DIST_DIR)
	svn export bin $(MATCHC_DIST_DIR)/bin $(SVN_FLAGS)
	svn export lib $(MATCHC_DIST_DIR)/lib $(SVN_FLAGS)
	svn export examples $(MATCHC_DIST_DIR)/examples $(SVN_FLAGS)
	mv $(MATCHC_DIST_DIR)/bin/matchC.py $(MATCHC_DIST_DIR)/bin/matchC
	rm $(MATCHC_DIST_DIR)/lib/fol.k

pack: install dist
	bash -c 'cd $(DIST_DIR); tar cvfz matchC.tar.gz matchC'

online: dist
	if [ $(LOCAL_HOST_NAME) = $(FSL_HOST_NAME) ]; \
  then \
    ( \
      rm -rf $(FSL_MATCHC_ONLINE_DIR); \
      cp -r $(MATCHC_DIST_DIR) $(FSL_MATCHC_ONLINE_DIR); \
      chmod -R a+w $(FSL_MATCHC_ONLINE_DIR); \
    ) \
  fi

test:
	find $(EXAMPLES_DIR) -type f -name '*.c' -exec bin/test_matchC.py "{}" \;

clean:
	$(MAKE) -C $(PARSER_DIR) clean
	$(MAKE) -C $(SEMANTICS_DIR) clean
	$(MAKE) -C $(VIEWER_DIR) clean
	rm -rf $(DIST_DIR)

