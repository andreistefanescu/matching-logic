#!/usr/bin/env bash
# cookbook filename: getopts_example
#
## using getopts
#
set -e
dumpFlag=
oflag=
usage="Usage: %s: [-o outputFileName] inputFileName\n"
oval=
warnFlag=
myDirectory=`dirname $0`
inputFile=
compileOnlyFlag=
function getoptsFunc {
	# echo "inside getopts"
	# echo "hmm"
	while getopts ':cdo:vw' OPTION
	do
		# echo "xxx $1"
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
	# echo "leaving getopts"
}
# echo "before getopts"
getoptsFunc "$@"
shift $(($OPTIND - 1))
# echo "after getopts"

# if [ "$aflag" ]
# then
  # printf "Option -a specified\n"
# fi

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
# printf "Remaining arguments are: %s\n" "$@"
shift 1

getoptsFunc "$@"
shift $(($OPTIND - 1))
# echo "after getopts"

maudeInput=$inputDirectory/$baseName.gen.maude
# echo "inputFile = $inputFile"
# echo "inputDirectory = $inputDirectory"
# echo "baseName = $baseName"
# echo "maudeInput = $maudeInput"
# echo "myDirectory = $myDirectory"
#make -f ../programs/Makefile -C ../programs $maudeInput
$myDirectory/compileProgram.sh $warnFlag $dumpFlag $inputFile
if [ ! "$?" ]; then
	echo "compilation failed"
	exit 2
fi
if [ ! "$compileOnlyFlag" ]; then 
	echo "load $myDirectory/c-total" > out.tmp
	echo "load program-$baseName-compiled" >> out.tmp
	#echo "rew in C-program-$baseName : eval(\"program-$baseName\"(.List{K}), \"$baseName\") ." >> out.tmp

	echo "--- &> /dev/null; if [ -t 0 ]; then stdin=\"\"; else stdin=\$(cat); fi; if [ \$DEBUG ]; then maude -no-wrap \$0; else (echo rew in C-program-$baseName : eval\\(\\\"program-$baseName\\\"\\(.List{K}\\), \\(\`for i in \$0 \"\$@\"; do echo \"\\\"String\\\" \\\"\$i\\\"(.List{K}),,\" ; done\` .List{K}\\), \\\"\$stdin\\\"\\) . | maude -no-wrap \$0 | perl /home/grosu/celliso2/matching-logic/trunk/ml-k/C/dist/wrapper.pl); fi ; exit \$?" > a.tmp
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
