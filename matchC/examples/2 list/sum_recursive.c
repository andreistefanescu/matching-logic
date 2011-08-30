/*
 * Function list_sum_recursive returns the sum of the elements of a
 * singly linked list. The sum is recursively computed.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


int list_sum_recursive(struct listNode* x)
//@ rule <k> $ => return sum(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  if (x == NULL)
    return 0;

  return x->val + list_sum_recursive(x->next);
}


/*@ var A : Seq */

