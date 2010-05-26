CIL_FLAGS="--noWrap --decil --noPrintLn --warnall --strictcheck --nokeepunused "
PEDANTRY_OPTIONS="-Wall -Wextra -Werror -Wmissing-prototypes -pedantic -x c -std=c99"
GCC_OPTIONS="-nostdlib -nodefaultlibs"
K_MAUDE_BASE=`readlink -f ~/k-framework/trunk`
K_PROGRAM_COMPILE="$K_MAUDE_BASE/tools/kcompile-program.sh"
myDirectory=`dirname $0`
set -e
if [ ! $1 ]; then
	echo "filename expected"
	exit 1
fi
filename=`basename "$1" .c`
if [ ! -e $filename.c ]; then
	echo "$filename.c not found"
	exit 1
fi

perl $myDirectory/embed.pl -d=ML -o=$filename.prepre.gen $filename.c
if [ ! $? -eq 0 ]; then 
	echo "Error"
	exit 1
fi
gcc $PEDANTRY_OPTIONS -E -I. -o $filename.pre.gen $filename.prepre.gen $myDirectory/fsl.h
rm -f $filename.prepre.gen
$myDirectory/cparser $CIL_FLAGS --out $filename.gen.maude.tmp $filename.pre.gen
#rm -f $filename.pre.gen
mv $filename.gen.maude.tmp $filename.gen.maude

echo "load $myDirectory/c-compiled" > program-$filename-gen.maude
echo "mod C-PROGRAM is" >> program-$filename-gen.maude
echo "including C-SYNTAX ." >> program-$filename-gen.maude
echo "including MATCH-C-SYNTAX ." >> program-$filename-gen.maude
echo "including COMMON-C-CONFIGURATION ." >> program-$filename-gen.maude
cat $filename.gen.maude >> program-$filename-gen.maude
rm -f $filename.gen.maude
echo -e "endm\n" >> program-$filename-gen.maude

$K_PROGRAM_COMPILE program-$filename-gen.maude C C-PROGRAM program-$filename
rm -f program-$filename-gen.maude
sed '1 d' program-$filename-compiled.maude > program-$filename-compiled.maude.tmp
mv program-$filename-compiled.maude.tmp program-$filename-compiled.maude

rm -f program-$filename-compiled.maude.tmp

