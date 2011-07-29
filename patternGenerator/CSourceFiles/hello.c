#include <stdio.h>

/*@ pattern simple<(y,x,z)> simpleheapyxz */
/*@ pattern simple<(x,z)> simpleheapxz */
struct elementary {
	int x;
	int y;
	int z;
};


/*@ pattern singlelinkedlist<(val),next> list */
struct listNode {
	int val;
	struct listNode * next;
};

//*@ pattern doublelinkedlist<(val,va,v),next,prev> dllist
struct dllistNode {
	int val;
	struct dllistNode* next;
	int va;
	struct dllistNode* prev;
	int v;
};

int main() {
	printf("Hello World!\n");
	return 0; 
}
