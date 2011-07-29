#include <stdlib.h>
#include <stdio.h>

/*@ pattern simple<(y,x,z)> simpleheapyxz */
/*@ pattern simple<(x,z)> simpleheapxz */
struct elementary {
	int x;
	int y;
	int z;
};

/*@ pattern singlelinkedlist<(val),nexts> lists */
struct listNodes {
	int val;
	struct listNodes * nexts;
};


/*@ pattern singlelinkedlist<nextd> lists */
/*@ pattern singlelinkedlist<(v,va,val),nextd> listd */
struct listNoded {
	int v;
	int va;
	int val;
	struct listNoded * nextd;
};

/*@ pattern singlelinkedlist<(val),next> list */
struct listNode {
	int val;
	struct listNode * next;
};


//@ pattern doublelinkedlist<(val,va,v),next,prev> dllist
struct dllistNode {
	int val;
	struct dllistNode* next;
	int va;
	struct dllistNode* prev;
	int v;
};



int main()
{
	struct listNode *x;
	struct listNode *y;
	
	return 0;
}
