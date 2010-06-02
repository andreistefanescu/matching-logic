#!/usr/bin/env bash
# cookbook filename: getopts_example
#
## using getopts
#
set -o errexit
set -o nounset
dumpFlag=
oflag=
usage="Usage: %s: [-o outputFileName] inputFileName\n"
oval=
warnFlag=
myDirectory=`dirname $0`
inputFile=
compileOnlyFlag=
function getoptsFunc {
	while getopts ':cdo:vw' OPTION
	do
		case $OPTION in
		c)	compileOnlyFlag="-c"
			;;
		d)	dumpFlag="-d"
			;;
		o)	oflag=1
			oval="$OPTARG"
			;;
		v)	printf "kcc version 0.0.1"
			exit 0
			;;
		w)	warnFlag="-w"
			;;
		?)	if [ ! -f $inputFile ]; then
				printf "$usage" $(basename $0) >&2
				exit 2
			fi
			;;
	  esac
	done
}
getoptsFunc "$@"
shift $(($OPTIND - 1))

if [ ! "$1" ]; then
	printf "$usage" $(basename $0) >&2
	exit 2
fi

inputFile=`readlink -f $1`
inputDirectory=`dirname $inputFile`
baseName=`basename $inputFile .c`

if [ ! "$oflag" ]; then
	if [ "$compileOnlyFlag" ]; then
		oval="$baseName.o"
	else
		oval="a.out"
	fi
fi

#printf "Compiling %s to %s\n" $inputFile $oval
if [ ! -f $inputFile ]; then
	printf "Input file %s does not exist\n" $inputFile
	exit 1
fi
shift 1

getoptsFunc "$@"
shift $(($OPTIND - 1))

maudeInput=$inputDirectory/$baseName.gen.maude
# echo "inputFile = $inputFile"
# echo "inputDirectory = $inputDirectory"
# echo "baseName = $baseName"
# echo "maudeInput = $maudeInput"
# echo "myDirectory = $myDirectory"
set +o errexit
$myDirectory/compileProgram.sh $warnFlag $dumpFlag $inputFile
if [ "$?" -ne 0 ]; then
	echo "compilation failed"
	exit 2
fi
set -o errexit
if [ ! "$compileOnlyFlag" ]; then
	echo "load $myDirectory/c-total" > out.tmp
	echo "load program-$baseName-compiled" >> out.tmp
	exec="echo rew in C-program-$baseName : eval\\(\\\"program-$baseName\\\"\\(.List{K}\\), \\(\`for i in \$0 \"\$@\"; do echo \"\\\"String\\\" \\\"\$i\\\"(.List{K}),,\" ; done\` .List{K}\\), \\\"\$stdin\\\"\\) . | maude -ansi-color -no-wrap \$0"
	echo "--- &> /dev/null; if [ -t 0 ]; then stdin=\"\"; else stdin=\$(cat); fi; if [ \$DEBUG ]; then $exec; else $exec | perl /home/grosu/celliso2/matching-logic/trunk/ml-k/C/dist/wrapper.pl; fi ; exit \$?" > a.tmp
	cat out.tmp | perl $myDirectory/slurp.pl >> a.tmp
	if [ ! "$dumpFlag" ]; then
		rm -f program-$baseName-compiled.maude
	fi
	chmod u+x a.tmp
	mv a.tmp $oval
else
	mv program-$baseName-compiled.maude $oval
fi

# clean up
rm -f out.tmp
rm -f a.tmp
