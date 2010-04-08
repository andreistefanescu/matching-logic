int main() {
	//@ assume nothing ;
	int sum = 0;
	//@ invariant nothing ;
	for(int i = 1; i <= 10; i++){
		sum += i;
	}
	//@ assert nothing ;
	return sum;
}
