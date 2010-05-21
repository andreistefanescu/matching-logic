use strict;
#open(MYINPUTFILE, "<quoted.maude");
# <STDIN> for standard in, <MYINPUTFILE> for a file

while(my $line = <STDIN>) {
	chomp($line);
	$line =~ s/metadata\((".*?")\)/metadata $1/; # removes parens from metadata
	$line =~ s/label\((.*?)\)/label $1/; # removes parens from label
	$line =~ s/prec\((\d*)\)/prec $1/; # removes parens from prec
	$line =~ s/^\s*none//; # removes none sections
	$line =~ s/nil -> /-> /; # removes nil op arguments
	$line =~ s/'([^ '"(),\]\[]+)\.([^ ,.\]\[]+)/($1)/g; # quoted constants
	$line =~ s/'"(([^"]|([\\]["]))*?)"\.([^ ,\]])/\("$1"\)\.$4/g; # string constants
	#$line =~ s/'"(([^\\"]|([\\]["])|([\\][^"]))*?)"\.[^ ,.\]\[]+/"$1"/g; # string constants
	$line =~ s/([^ `])\[/$1\(/g; # changes [ into (
	$line =~ s/\] \./FSLENDLQQQ/; # saves attribute brackets
	while ($line =~ s/([^`])\]/$1\)/g){ } # changes ] into )
	while ($line =~ s/sorts ([^ ]*?) ;/sort $1 . sorts/g){}
	$line =~ s/FSLENDLQQQ/\] \./; # replaces attribute brackets
	$line =~ s/\[none\]//g; # remove [none] attributes
	$line =~ s/'([^ )(,\[\]\{\}]+)/$1/g; # removes all other quotes
	print "$line\n";
}