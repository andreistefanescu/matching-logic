use strict;
my $state = "start";
my $retval = -1;

while (my $line = <STDIN>) {
	chomp($line);
	if ($state eq "start"){
		if ($line =~ m/^rewrite in /){
			$state = "rewrite";
			#printf "REWRITE\n";
		}
	} elsif ($state eq "rewrite"){
		$line = <STDIN>;
		if ($line =~ m/^result NeBag:/){
			$state = "success";
			#printf "SUCCESS\n";
		} else {
			$state = "failure";
			printf "FAILURE\n";
		}
	} elsif ($state eq "success"){
		if ($line =~ m/< input > <\/ input >/){
		} elsif ($line =~ m/< output > "String" (.*)\(\.List{K}\) <\/ output >/){
			my $output = $1;
			$output =~ s/%/%%/;
			print `printf $output`;
		} elsif ($line =~ m/< resultValue > \("tv"\)\.KResultLabel\("Rat" (\d+)\(\.List{K}\),,"Base-Type" int\(\.List{K}\)\) <\/ resultValue >/){
			$retval = $1;
			#print "xxx$retval\n";
		}
		
	} 
	
	if ($state eq "failure"){
		print "$line\n";
	}
}
#print "yyy$retval\n";
exit $retval;