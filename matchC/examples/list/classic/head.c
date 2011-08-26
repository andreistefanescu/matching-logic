/*
 * Function separating a list into its head and rest of the list.
 * It returns the first element.
 */


#include <stdlib.h>


struct listNode {
	int val;
	struct listNode *next;
};



int head(struct listNode *a)
/*@ rule <k> $ => return val; ...</k>
         <heap>... list(a)([val] @ A) ...</heap> */
{
  return a->val;
}


//@ var val : Int
//@ var A : Seq
