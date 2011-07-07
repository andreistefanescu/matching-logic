/* hello.c -- The most famous program of them all ..
 */

#include <stdio.h>
/*@ pattern singlelinkedlist<(y,a,b,c),z> hellolist */
struct name { int x;
	
	
	int y;
	
	struct name    * z;
	
	int a;
	int b;
	int c;
	
	
}    ;

int main() {
	printf("Hello World!\n");
	return 0; 
}
