int main() {
	return sum(10);
}

int sum(int n) {
	int sum = 0;
	//@ assume < T > < env > @n |-> ?l1 @sum |-> ?l2 </ env > < mem > ?l1 |-> ?n ?l2 |-> ?sum </ mem > < form > TrueFormula </ form > </ T >
	int i = 1;
	//@ invariant .Bag
	while (i <= n){
		sum += i;
		i++;
	}
	//@ assert .Bag
	return sum;
}
