/* hello.c -- The most famous program of them all ..
 */

#include <stdio.h>

/*@ map2hpattern
	pattern doublelinkedlist
	name dllist
	next t
	previous t
 */
struct structure {
	int x;
	int y;
	struct structure* z;
	struct structure* t;
}    ;

int main() {
	printf("Hello World!\n");
	return 0; 
}
