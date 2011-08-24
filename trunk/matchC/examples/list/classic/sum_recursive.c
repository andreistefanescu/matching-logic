/*
 * The example computes the sum of the elements of a list
 * received as argument for the function.
 * The function is recursive.
 */

#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


int list_sum(struct listNode* x)
//@ rule <k> $ => return sum(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  if (x == 0) {
    return 0;
  }
  else {
    return x->val + list_sum(x->next);
  }

}


/*@ var A : Seq */
