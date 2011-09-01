/*
 * Function that deletes the second element of a circular list.
 */


#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* circular_list_pop(struct listNode* x)
/*@ rule <k> $ => return x; ...</k>
         <heap>... x |-> [vx, n], lseg(n,x)([v] @ A) =>
                   x |-> [vx, ?n], lseg(?n,x)(A) ...</heap>
 */
{
  struct listNode* t;

  t = x->next;
  x->next = t->next;
  free(t);
  return x;
}

//@ var A : Seq
//@ var n, vx, v : Int
