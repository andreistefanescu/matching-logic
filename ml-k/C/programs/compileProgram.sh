CIL_FLAGS="--noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused "
PEDANTRY_OPTIONS="-Wall -Wextra -Werror -Wmissing-prototypes -pedantic -x c -std=c99"
GCC_OPTIONS="-nostdlib -nodefaultlibs"
K_MAUDE_BASE=`readlink -f ~/k-framework/trunk`
K_PROGRAM_COMPILE="$K_MAUDE_BASE/tools/kcompile-program.sh"
myDirectory=`dirname $0`
set -o nounset

dflag=
nowarn=0
usage="Usage: %s: [-d] inputFileName\n"
while getopts 'dw' OPTION
do
	case $OPTION in
	d)	dflag=1
		;;
	w)	nowarn=1
		;;
	?)	printf "$usage" $(basename $0) >&2
		exit 2
		;;
  esac
done
shift $(($OPTIND - 1))

if [ ! "$1" ]; then
	echo "filename expected"
	exit 2
fi
filename=`basename "$1" .c`
directoryname=`dirname "$1"`/
if [ ! -e $directoryname$filename.c ]; then
	echo "$filename.c not found"
	exit 1
fi

perl $myDirectory/embed.pl -d=ML -o=$filename.prepre.gen $directoryname$filename.c
if [ "$?" -ne 0 ]; then 
	echo "Error generating ML annotations."
	exit 1
fi
gcc $PEDANTRY_OPTIONS $GCC_OPTIONS -E -I. -I$myDirectory $filename.prepre.gen $myDirectory/clib.h > $filename.pre.gen 2> $filename.warnings.log
if [ "$?" -ne 0 ]; then 
	echo "Error running preprocessor:"
	cat $filename.warnings.log >&2
	exit 1
fi
if [ ! "$nowarn" ]; then
	cat $filename.warnings.log >&2
fi
#echo "done with gcc"
if [ ! "$dflag" ]; then
	rm -f $filename.prepre.gen
fi
$myDirectory/cparser $CIL_FLAGS --out $filename.gen.maude.tmp $filename.pre.gen 2> $filename.warnings.log
if [ "$?" -ne 0 ]; then 
	echo "Error running cil"
	exit 1
fi
if [ ! "$nowarn" ]; then
	cat $filename.warnings.log >&2
fi
rm -f $filename.warnings.log
#echo "done with cil"
if [ ! "$dflag" ]; then
	rm -f $filename.pre.gen
fi
mv $filename.gen.maude.tmp $filename.gen.maude

echo "load $myDirectory/c-total" > program-$filename-gen.maude
echo "mod C-PROGRAM is" >> program-$filename-gen.maude
echo "including C-SYNTAX ." >> program-$filename-gen.maude
echo "including MATCH-C-SYNTAX ." >> program-$filename-gen.maude
echo "including COMMON-C-CONFIGURATION ." >> program-$filename-gen.maude
cat $filename.gen.maude >> program-$filename-gen.maude
if [ ! "$dflag" ]; then
	rm -f $filename.gen.maude
fi
echo -e "endm\n" >> program-$filename-gen.maude

$K_PROGRAM_COMPILE program-$filename-gen.maude C C-PROGRAM program-$filename >> compilation.log
if [ "$?" -ne 0 ]; then 
	echo "Error compiling program"
	exit 1
fi
if [ ! "$dflag" ]; then
	rm -f program-$filename-gen.maude
fi
sed '1 d' program-$filename-compiled.maude > program-$filename-compiled.maude.tmp
mv program-$filename-compiled.maude.tmp program-$filename-compiled.maude

rm -f program-$filename-compiled.maude.tmp

