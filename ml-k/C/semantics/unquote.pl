use strict;
open(MYINPUTFILE, "<quoted.maude");

while(my $line = <MYINPUTFILE>) {
	chomp($line);
	$line =~ s/metadata\((".*?")\)/metadata $1/;
	$line =~ s/label\((.*?)\)/label $1/;
	$line =~ s/prec\((\d*)\)/prec $1/g;
	$line =~ s/^\s*none//;
	$line =~ s/nil -> /-> /;
	while ($line =~ s/'([^ '"()\]\[]+?)\.([^ ,.\]\[]+)/($1)/g){} # quoted constants
	$line =~ s/'"(([^"]|([\\]["]))*?)"\.([^ ,\]])/\("$1"\)\.$4/g; # string constants
	# '"\n %c %c %c %d".String
	$line =~ s/([^ `])\[/$1\(/g; # changes [ into (
	$line =~ s/\] \./FSLENDLQQQ/g;
	while ($line =~ s/([^`])\]/$1\)/g){ } # changes ] into )
	while ($line =~ s/sorts ([^ ]*?) ;/sort $1 . sorts/g){}
	$line =~ s/FSLENDLQQQ/\] \./g;
	$line =~ s/\[none\]//g; # remove [none] attributes
	$line =~ s/'([^ )(,\[\]\{\}]+)/$1/g;
	print "$line\n";
	# crl _`(_`)(("_^_").KProperLabel,_`,`,_(_`(_`)(
	# ("tv").KResultLabel,_`,`,_(_`(_`)("Rat"_(I1:Int),(.List`{K`}).List`{K`}),T:KResult))
	# ,_`(_`)(("tv").KResultLabel,_`,`,_(_`(_`)("Rat"_(I2:Int),(.List`{K`}).List`{K`}),T:KResult)))) 
	# => _`(_`)(("cast").KProperLabel,_`,`,_(T:KResult,_`(_`)("Rat"_(_xorInt_(I1:Int,I2:Int)),
	# (.List`{K`}).List`{K`}))) 
	# if (_contains_((integerTypes)).Set,T:KResult) = (true).Bool [metadata "computational rule"] .
	# '.List`{K`}.List`{K`}
	
	# '0.Zero
	
	#eq '<_>_</_>['k.CellLabel,'_~>_[
	# '_`(_`)[
	# '"&_".KProperLabel,'_`(_`)[
	# '"_->_".KProperLabel,'_`,`,_[
	# 'Kcxt:KProper,'_`(_`)[
	# '"Id"_['X:Id],'.List`{K`}.List`{K`}]]]],'Rest:K],'k.CellLabel] = '<_>_</_>['k.CellLabel,'_~>_['Kcxt:KProper,'_`(_`)['freezer['"(\"&_\").KProperLabel((\"_->_\").KProperLabel(`[HOLE`]:K,,\"Id\"X:Id(.List{K})))".String],'_`(_`)['freezeVar['"X:Id".String],'_`(_`)['"Id"_['X:Id],'.List`{K`}.List`{K`}]]],'Rest:K],'k.CellLabel] [metadata("heating")] .
	
	# Kcxt:KResult)],'Rest
# crl '_`(_`)['"~_".KProperLabel,'_`(_`)['"tv".KResultLabel,'_`,`,_['_`(_`)['"Rat"_['I:Int],'.List`{K`}.List`{K`}],'T:KResult]]] 
# => '_`(_`)['"cast".KProperLabel,'_`,`,_['T:KResult,'_`(_`)['"Rat"_['~Int_['I:Int]],'.List`{K`}.List`{K`}]]] 
# if '_contains_['integerTypes.Set,'T:KResult] = 'true.Bool [metadata("computational rule")] .

}