/*
 * Function list_cons appends an integer value to a singly-linked list.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* list_cons(struct listNode* x, int v)
/*@ rule <k> $ => return ?x; ...</k> 
         <heap>... list(x)(A) => list(?x)([v] @ A) ...</heap> */
{
  struct listNode* y;

  y = (struct listNode*) malloc (sizeof(struct listNode));
  y->val = v;
  y->next = x;

  return y;
}


//@ var A : Seq

