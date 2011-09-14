#include <stdlib.h>
#include <stdio.h>

/* pattern tuple<(x,y,z)> tuplexyz */
/* pattern tuple<(x,z)> tuplexz */
/* pattern tuple<()> emptytuple */
struct elementary {
	int x;
	int y;
	int z;
};


/* pattern singlelinkedlist<(),next> list */
/*@ pattern singlelinkedlist<(a,b,c),next> listabc */
/* pattern singlelinkedlist<(a,c),next> listac */
struct listNode {
	int a;
	int b;
	int c;
	struct listNode* next;
};


// pattern doublelinkedlist<(x,y,z),next,prev> dllist
struct dllistNode {
	int x;
	struct dllistNode* next;
	int y;
	struct dllistNode* prev;
	int z;
};

// pattern binarytree<(val),left,right> btree
struct btreenode {
	struct btreenode* left;
	struct btreenode* right;
	int val;
};

int main()
{
  struct listNode *x;
  return 0;
}
