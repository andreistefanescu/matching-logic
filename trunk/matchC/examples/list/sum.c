#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

int list_sum(struct listNode* x)
//@ rule <k> $ => return sum(A); </k> <heap_> list(x)(A) <_/heap>
{
  int s;
  
  s = 0;
  /*@ inv <heap_> lseg(old(x), x)(?A1), list(x)(?A2) <_/heap> 
          /\ A = ?A1 @ ?A2 /\ s = sum(?A1) */
  while (x != NULL) {
    s += x->val;
    x = x->next;
  }

  return s;
}


/*@ var A : Seq */

