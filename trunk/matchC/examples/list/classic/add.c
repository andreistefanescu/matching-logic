/*
 * Function adding a new node with a given integer value
 * to the beginning of a list.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* add(struct listNode* x, int i)
/*@ rule <k> $ => return ?x; ...</k> 
         <heap>... 
             list(x)(A) 
			 => 
             list(?x)([i] @ A) 
         ...</heap> */
{
  struct listNode* y;
  y = (struct listNode*) malloc (sizeof(struct listNode));
  y->val = i;
  y->next = x;
  return y;
}

//@ var A : Seq

