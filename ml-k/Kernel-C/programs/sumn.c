int main() {
	//@ assume <config> <env> n |-> n0 ;; s |-> 0 </env> <heap> .Heap </heap> <form> @(n0 >=Int 0) </form> </config> ;
	int sum = 0;
	//@ invariant <config> <env> n |-> ?n ;; s |-> (((n0 +Int (-Int ?n)) *Int (n0 +Int ?n +Int 1)) /Int 2) </env> <heap> .Heap </heap> <form> @(?n >=Int 0) /\\ @(n0 >=Int 0) </form> </config> ;
	for(int i = 1; i <= 10; i++){
		sum += i;
	}
	//@ assert <config> <env> n |-> 0 ;; s |-> ((n0 *Int (n0 +Int 1)) /Int 2) </env> <heap> .Heap </heap> <form> @(n0 >=Int 0) </form> </config> ;
	return sum;
}
