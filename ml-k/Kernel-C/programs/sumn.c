int main() {
	//@ assume < T > < env > .Map </ env > < mem > .Map </ mem > < form > @ </ form > </ T >
	int sum = 0;
	//@ invariant .Bag
	for(int i = 1; i <= 10; i++){
		sum += i;
	}
	//@ assert .Bag
	return sum;
}
