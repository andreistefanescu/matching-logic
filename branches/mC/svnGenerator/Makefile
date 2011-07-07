# add java (.java, and .class), and antlr (.g, and .tokens) extensions
# to the list of known file extentions
.SUFFIXES: .java .class .g

# generic 
JC = javac
JVM = java
JAR = jar
CLASSPATH = ./sourcefiles/
JFLAGS = -classpath $(CLASSPATH)

# compile a .java file into one or more .class files
.java.class:
	$(JC) $(JFLAGS) $<


JAVA_SOURCES = sourcefiles/StructMetaInfo.java \
sourcefiles/CStructure.java \
sourcefiles/CStructures.java \
sourcefiles/GeneralFunctions.java \
sourcefiles/CProcessor.java \
sourcefiles/BinaryTreeGenerator.java \
sourcefiles/DoubleLinkedListGenerator.java \
sourcefiles/SingleLinkedListGenerator.java \
sourcefiles/ElementaryFieldsOnlyGenerator.java \
sourcefiles/MathObjUpleGenerate.java \
sourcefiles/ParametrizedPatterns.java

CLASSES = $(JAVA_SOURCES:.java=.class)
PP_JAR = PP.jar


# targets
# default target is all
all: build

# build target
build: $(PP_JAR)

# build a jar
$(PP_JAR): $(CLASSES)
	$(JAR) -cf $@ sourcefiles/*.class

# run target (depends on build)
run: build
	$(JVM) $(JFLAGS) ParametrizedPatterns $(ARG)

# clean target removes the .class files
clean:
	rm -rf $(PP_JAR) *.class
	rm -rf *.k
	rm -rf *.maude

