use strict;
use DBI;
my $dbh = DBI->connect("dbi:SQLite:dbname=maudeProfileDBfile.sqlite","","");
$dbh->do("DROP TABLE IF EXISTS data;");
$dbh->do("CREATE TABLE data (rule NOT NULL, type NOT NULL, rewrites BIGINT NOT NULL, matches NULL DEFAULT NULL, fragment NULL DEFAULT NULL, initialTries NULL DEFAULT NULL, resolveTries NULL DEFAULT NULL, successes NULL DEFAULT NULL, failures NULL DEFAULT NULL)");
#$dbh->do( "INSERT INTO data (rule, type, rewrites) VALUES ( 'test', 'op', 5 ) " );
 
# $dbh->do( "INSERT INTO authors VALUES ( 'Conway', 'Damian' ) " );
# $dbh->do( "INSERT INTO authors VALUES ( 'Booch', 'Grady' ) " );
# $dbh->do( "CREATE TABLE books ( title, author )" );
# $dbh->do( "INSERT INTO books VALUES ( 'Object Oriented Perl',
										 # 'Conway' ) " );
# $dbh->do( "INSERT INTO books VALUES ( 'Object-Oriented Analysis and Design',
										 # 'Booch' ) ");
# $dbh->do( "INSERT INTO books VALUES ( 'Object Solutions', 'Booch' ) " );

open(MYINPUTFILE, "<profile.log");
my $line = <MYINPUTFILE>;
# skip header if it's there
if (index($line,"\||||||||||||||||||/") != -1){
	$line = <MYINPUTFILE>; $line = <MYINPUTFILE>;
	$line = <MYINPUTFILE>; $line = <MYINPUTFILE>;
	$line = <MYINPUTFILE>; $line = <MYINPUTFILE>;
}

#print "a\n";
# after first ==========================================
while($line = nextBlock(*MYINPUTFILE)) {
	#print "$line\n";
	if ($line =~ m/^op /){
		handleOp($line, *MYINPUTFILE);
	}
}

# Print the line to the screen and add a newline
my $res = $dbh->selectall_arrayref( q( 
SELECT a.rule, a.type, a.rewrites 
FROM data a
ORDER BY a.rewrites DESC
) );
foreach(@$res) {
	foreach my $i (0..$#$_) {
		print "$_->[$i] "
	}
	print "\n";
}

$dbh->disconnect;

sub nextBlock {
	my ($file) = @_;
	while(<$file>) {
		my $line = $_;
		chomp($line);
		if ($line =~ m/^op /){
			return $line;
		} else {
			next;
		}
	}
	return 0;
}

sub handleOp {
	my ($line, $file) = @_;
	if ($line eq "") { return; }
	my $op = substr($line, 3);
	$line = <$file>;
	if ($line =~ m/: (\d+) \(/){
		my $rewrites = $1;
		$dbh->do( "INSERT INTO data (rule, type, rewrites) VALUES ( '$op', 'op', $rewrites ) " );
	}
	
	
	# while(<$file>) {
		# my $line = $_;
		# chomp($line);
		# if ($line =~ m/^op /){
			# return $line;
		# } else {
			# next;
		# }
	# }
	
	#
	
	return 0;
}
