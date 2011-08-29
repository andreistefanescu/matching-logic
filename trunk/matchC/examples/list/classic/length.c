/*
 * Function list_length returns the length of a singly-linked list.  The length
 * is iteratively computed.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


int list_length(struct listNode* x)
//@ rule <k> $ => return len(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  int l;
  
  l = 0;
  /*@ inv <heap>... lseg(old(x), x)(?A1), list(x)(?A2) ...</heap>
          /\ A = ?A1 @ ?A2 /\ l = len(?A1) */
  while (x != NULL) {
    l += 1;
    x = x->next;
  }

  return l;
}


//@ var A : Seq

