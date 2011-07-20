# add java (.java, and .class) extensions to the list of known file extensions
.SUFFIXES: .java .class

# generic 
JC = javac
JVM = java
JAR = jar
CLASSPATH = .
JFLAGS = -classpath $(CLASSPATH)

# compile a .java file into one or more .class files
.java.class:
	$(JC) $(JFLAGS) $<


JAVA_SOURCES = StructMetaInfo.java \
CStructure.java \
CStructures.java \
GeneralFunctions.java \
CProcessor.java \
BinaryTreeGenerator.java \
DoubleLinkedListGenerator.java \
SingleLinkedListGenerator.java \
ElementaryFieldsOnlyGenerator.java \
SimpleStructureGenerator.java \
MathObjUpleGenerate.java \
ParametrizedPatterns.java

CLASSES = $(JAVA_SOURCES:.java=.class)
PP_JAR = PP.jar


# targets
# default target is all
all: build

# build target
build: $(PP_JAR)

# build a jar
$(PP_JAR): $(CLASSES)
	$(JAR) -cf $@ *.class

# run target (depends on build)
run: build
	$(JVM) $(JFLAGS) ParametrizedPatterns

# clean target removes the .class files
clean:
	rm -rf $(PP_JAR) *.class

