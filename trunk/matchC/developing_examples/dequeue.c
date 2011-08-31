/*
 * Function that removes the first element from the content of a queue.
 */


#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct queueNode {
  struct listNode* head;
  struct listNode* tail;
};


struct queueNode* dequeue(struct queueNode *x)
/*@ rule <k> $ => return x; ...</k> 
         <heap>... queue(x)([val] @ A) => queue(x)(A) ...</heap>
    if ~(x = 0) */
{
  struct listNode* n;

  if (x->head != 0)
  {
    n = x->head;
    if (x->head == x->tail)
    {
      x->head = n->next;
      x->tail = n->next;
    }
    else x->head = n->next;
  }
  free(n);
  return x;
}

//@ var val : Int
//@ var A : Seq
