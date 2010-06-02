use strict;
my $state = "start";
my $retval = -1;
my $reduced = 0;
my $buffer = "";
while (my $line = <STDIN>) {
	$buffer .= $line;
	chomp($line);
	$line =~ s/[\000-\037]\[(\d|;)+m//g;
	#print "$line\n";
	if ($state eq "start"){
		if ($line =~ m/^rewrite in /){
			$state = "rewrite";
			#printf "REWRITE\n";
		}
	} elsif ($state eq "rewrite"){
		$line = <STDIN>;
		$buffer .= $line;
		$line =~ s/[\000-\037]\[(\d|;)+m//g;
		#print "$line\n";
		if ($line =~ m/^result NeBag:/){
			$state = "success";
			#printf "SUCCESS\n";
		} else {
			$state = "failure";
			printf "FAILURE\n";
		}
	} elsif ($state eq "success"){
		if ($line =~ m/< (input|\(input\)\.CellLabel) > .* <\/ \1 >/){
			$reduced = 1;
		} elsif ($line =~ m/< (output|\(output\)\.CellLabel) > "String" (.*)\(\.List{K}\) <\/ \1 >/){
			my $output = $2;
			$output =~ s/\%/\%\%/g;
			$output =~ s/\\\\/\\\\\\\\/g;
			print `printf $output`;
		} elsif ($line =~ m/< (resultValue|\(resultValue\)\.CellLabel) > \("tv"\)\.KResultLabel\("Rat" (-?\d+)\(\.List{K}\),,"Base-Type" int\(\.List{K}\)\) <\/ \1 >/){
			$retval = $2;
		}
	} 
	
	if ($state eq "failure"){
		print "$line\n";
	}
}
if ($reduced == 0) {
	print "$buffer\n";
}
exit $retval;