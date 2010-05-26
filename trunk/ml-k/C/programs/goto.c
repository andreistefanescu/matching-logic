#include <stdio.h>

int gotowhile(void){
	int flag;
	flag = 1;
	
	if (flag) {
		goto target;
	}
	
	while (0){
		int local = 1;
		printf("local=%d\n", local);
	target:
		local = 0;
		printf("local=%d\n", local);
	}
	return 0;
}

int gotoloop(void){
	int n=10;
loop:
	printf("%d, ", n);
	n--;
	if (n>0) { 
		goto loop;
	}
	puts("Done!");
	return 0;
}

int sneaky(void){
	int loopGuard = 0;
	while (loopGuard == 0){
		goto sneaky;
		
		if (loopGuard != 0){
	sneaky:
			puts("sneaky");
			loopGuard = 1;
		} else {
			loopGuard = 0;
		}
	}
	return 0;
}

int last(void){
	int last = 0;
	int x = 5;
start:
	while (last < 5){
		last++;
		printf("%d, ", last);
		goto last;
	}
	goto end;
	last:
		goto start;
	end:
	return 0;
}

int another(void){
	int another = 5;
	goto insideLoop;
	another = 60;
	while (another > 0){
	insideLoop:
		printf("%d, ", another);
		another--;
	}
	puts("");
	return 0;
}

int myswitch(void){
	unsigned count;
	unsigned x;

	count = 2;
	printf ("The count is %d.  \nThis is ", count);
	switch (count) {
		case 0:
			printf ("none.\n");
			goto next;
		case 1:
			printf ("only one.\n");
			goto next;
		case 2:
			printf ("a pair.\n");
			goto next;
		case 3:
			printf ("three.\n");
			goto next;
		default:
			printf ("many.\n");
			goto next;
	}
	next:

	x = 4;
	printf ("The test number is %d.\n", x);
	while (x < 10) {
		++x;
		if (x % 2 == 0) {
			goto done;
		}
		printf ("%d is an odd number.\n", x);
	}
	done:
	return 0;
}

	
int main(void){
	gotowhile();	
	gotoloop();	
	sneaky();
	myswitch();
	another();
	int retval = last();
	
	return retval;
}
