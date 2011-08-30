/*
 * Function list_head returns the head of a singly linked list. The
 * specification requires the list to have at least one element.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


int list_head(struct listNode *x)
//@ rule <k> $ => return v; ...</k> <heap>... list(x)([v] @ A) ...</heap>
{
  return x->val;
}


//@ var v : Int
//@ var A : Seq

