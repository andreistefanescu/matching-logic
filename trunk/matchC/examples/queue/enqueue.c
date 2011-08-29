/*
 * Function that add a new element to the queue - a new integer
 * value is added to the content of the queue.
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


struct queueNode* enqueue(struct queueNode *x, int val)
/*@ rule <k> $ => return x; ...</k>
         <heap>... queue(x)(A) => queue(x)([val] @ A) ...</heap>
    if ~(x = 0) */
{
  struct listNode* n;
  n = (struct listNode*)malloc(sizeof(struct listNode));
  n->val = val;
  n->next = 0;
  x->tail = x->tail;
  x->tail->next = x->tail->next;
	
  if (x->head != 0)
  {
    x->tail->next = n ;
  }
  else 
  {
    x->head = n ;
  }
  x->tail = n;
	
  return x;
}


//@ var A : Seq
