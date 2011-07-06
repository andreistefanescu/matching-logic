#include <stdio.h>

/*@ pattern doublelinkedlist<(x,y),t,z> dlinkedlist */
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
