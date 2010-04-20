int sum(int n);
int main() {
	return sum(10);
}

int sum(int n) {
	//@ pre < T > < env > @n |-> ?l1 </ env > < mem > ?l1 |-> #n0 </ mem > < form > TrueFormula </ form > </ T >
	int sum = 0;
	int i = 1;
	//@ invariant < T > < env > @n |-> ?l1 @sum |-> ?l2 </ env > < mem > ?l1 |-> ?n ?l2 |-> (((#n0 +Int (-Int ?n)) *Int (#n0 +Int ?n +Int 1)) /Int 2) </ mem > < form > TrueFormula </ form > </ T >
	// xx @(?n >=Int 0) /\ @(#n0 >=Int 0)
	while (i <= n){
		sum += i;
		i++;
	}
	//@ post .Bag
	return sum;
}
