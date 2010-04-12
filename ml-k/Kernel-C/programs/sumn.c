int main() {
	return sum(10);
}

int sum(int n) {
	//@ assume < T > < env > .Map </ env > < mem > .Map </ mem > < form > @ </ form > </ T >
	int sum = 0;
	int i = 1;
	//@ invariant .Bag
	while (i <= n){
		sum += i;
		i++;
	}
	//@ assert .Bag
	return sum;
}
