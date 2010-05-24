int sum(int n);
int main() {
	//@xxx pre ?Bag
	return sum(10);
	//@xxx post ?Bag
}

int sum(int n) {
	//@xxx pre < T > < env > @n |-> ?l1 </ env > < mem > ?l1 |-> #n0 </ mem > < form > TrueFormula </ form > </ T >
	int sum = 0;
	int i = 1;
	//@xxx invariant < T > < env > @n |-> ?l1 @sum |-> ?l2 </ env > < mem > ?l1 |-> ?n ?l2 |-> (((#n0 +Int (-Int ?n)) *Int (#n0 +Int ?n +Int 1)) /Int 2) </ mem > < form > TrueFormula </ form > </ T >
	// xx @(?n >=Int 0) /\ @(#n0 >=Int 0)
	while (i <= n){
		sum += i;
		i++;
	}
	//@xxx post .Bag
	return sum;
}
