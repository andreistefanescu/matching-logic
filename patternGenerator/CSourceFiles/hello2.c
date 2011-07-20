/* hello.c -- The most famous program of them all ..
 */

#include <stdio.h>

/*@ pattern doublelinkedlist<(x,y),z,t> dllisthello */
struct structure {
	int x;
	int y;
	struct structure* z;
	struct structure* t;
}    ;

/*@ pattern doubleinkedlist<(x,y),z,t> dllisthello */
struct structurename {
	int x;
	int y;
	struct structure* z;
	struct structure* t;
}    ;

int main() {
	printf("Hello World!\n");
	return 0; 
}
