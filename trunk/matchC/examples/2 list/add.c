/*
 * Function list_add appends an integer value to the beginning of a singly
 * linked list.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* list_add(int v, struct listNode* x)
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

