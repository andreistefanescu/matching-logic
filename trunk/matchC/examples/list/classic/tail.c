/*
 * Function separating a list into its head and rest of the list. It returns 
 * the first element of the rest of the list.
 */


#include <stdlib.h>


struct listNode {
	int val;
	struct listNode *next;
};


struct listNode* tail(struct listNode *a)
/*@ rule <k> $ => return ?b; ...</k> 
         <heap>... list(a)([val] @ A) => list(a)([val]), list(?b)(A) ...</heap> */
{
	struct listNode *b;
	
	b = a->next;
	a->next = 0;
	
	return b;
}


//@ var val, b : Int
//@ var A : Seq
