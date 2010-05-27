#!/usr/bin/env bash
# cookbook filename: getopts_example
#
## using getopts
#
set -e
dflag=
oflag=
usage="Usage: %s: [-o outputFileName] inputFileName\n"
while getopts ':do:v' OPTION
do
	case $OPTION in
	d)	dflag=1
		;;
	o)	oflag=1
		oval="$OPTARG"
		;;
	v)	printf "kcc version 0.0.1"
		exit 0
		;;
	?)	printf "$usage" $(basename $0) >&2
		exit 2
		;;
  esac
done
shift $(($OPTIND - 1))

# if [ "$aflag" ]
# then
  # printf "Option -a specified\n"
# fi
if [ ! "$oflag" ]; then
	oval="a.out"
fi
if [ ! "$1" ]; then
	printf "$usage" $(basename $0) >&2
	exit 2
fi

inputFile=`readlink -f $1`
inputDirectory=`dirname $inputFile`
baseName=`basename $inputFile .c`
myDirectory=`dirname $0`
#printf "Remaining arguments are: %s\n" "$1"
#printf "Compiling %s to %s\n" $inputFile $oval
if [ ! -f $inputFile ]; then
	printf "Input file %s does not exist\n" $inputFile
	exit 1
fi

maudeInput=$inputDirectory/$baseName.gen.maude
#echo "inputFile = $inputFile"
#echo "inputDirectory = $inputDirectory"
#echo "baseName = $baseName"
#echo "maudeInput = $maudeInput"

#make -f ../programs/Makefile -C ../programs $maudeInput
if [ "$dflag" ]; then
	$myDirectory/compileProgram.sh -d $inputFile
else
	$myDirectory/compileProgram.sh $inputFile
fi
echo "load $myDirectory/c-compiled" > out.tmp
echo "load program-$baseName-compiled" >> out.tmp
echo "rew in C-program-$baseName : eval(\"program-$baseName\"(.List{K}), \"$baseName\") ." >> out.tmp

echo "--- &> /dev/null; if [ \$DEBUG ]; then maude -no-wrap \$0; else (echo q | maude -no-wrap \$0 | perl $myDirectory/wrapper.pl); fi ; exit \$?" > a.tmp
cat out.tmp | perl $myDirectory/slurp.pl >> a.tmp
if [ ! "$dflag" ]; then
	rm -f program-$baseName-compiled.maude
fi
#echo q >> a.tmp
chmod u+x a.tmp
mv a.tmp $oval

# clean up
rm -f out.tmp
rm -f a.tmp
