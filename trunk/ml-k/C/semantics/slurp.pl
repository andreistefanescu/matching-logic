use strict;
use File::Basename;

slurp(*STDIN, './');

sub slurp {
	my ($file, $path) = (@_);
	while (my $line = <$file>){
		chomp($line);
		if ($line =~ m/\s*load "?([^\s"]*)"?/) {
			my ($filename,$dirname,$suffix) = fileparse($1,".maude");
			$filename = "$dirname$filename.maude";
			if (!(-e $filename)) {
				$filename = "$path$filename";
			}
			#print "file = $filename\n";
			#print "dirname = $dirname\n";
			my $newFile;
			open($newFile, $filename) or die "Couldn't open file $filename\n";
			slurp($newFile, $dirname);
		} else {
			print "$line\n";
		}
	}
	#print "done with $file\n";
}
