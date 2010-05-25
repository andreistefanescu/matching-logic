#!/usr/bin/env bash
# cookbook filename: getopts_example
#
## using getopts
#
aflag=
oflag=
while getopts 'ao:' OPTION
do
  case $OPTION in
  a)	aflag=1
		;;
  o)	oflag=1
		oval="$OPTARG"
		;;
  ?)	printf "Usage: %s: [-o value] args\n" $(basename $0) >&2
		exit 2
		;;
  esac
done
shift $(($OPTIND - 1))

# if [ "$aflag" ]
# then
  # printf "Option -a specified\n"
# fi
if [ "$oflag" ]; then
	printf 'Option -o "%s" specified\n' "$oval"
else
	oval="a.out"
fi
inputFile=`readlink -f $1`
inputDirectory=`dirname $inputFile`
baseName=`basename $inputFile .c`
#printf "Remaining arguments are: %s\n" "$1"
printf "Compiling %s to %s\n" $inputFile $oval
if [ ! -f $inputFile ]; then
	printf "Input file %s does not exist\n" $inputFile
	exit 1
fi

maudeInput=$inputDirectory/$baseName.gen.maude
echo "inputFile = $inputFile"
echo "inputDirectory = $inputDirectory"
echo "baseName = $baseName"
echo "maudeInput = $maudeInput"

make -f ../programs/Makefile -C ../programs $maudeInput
echo "load c-compiled" > out.tmp
echo "load c-syntax" >> out.tmp
echo "load common-c-configuration" >> out.tmp
echo "load program-$baseName-compiled" >> out.tmp
echo "rew in C-program-$baseName : eval(\"program-$baseName\"(.List{K}), \"$baseName\") ." >> out.tmp

echo "--- &> /dev/null; (maude -no-wrap \$0 | perl wrapper.pl) ; exit \$?" > a.tmp
cat out.tmp | perl slurp.pl >> a.tmp
echo q >> a.tmp
chmod u+x a.tmp
mv a.tmp $oval

clean:
	rm out.tmp
	rm a.tmp
