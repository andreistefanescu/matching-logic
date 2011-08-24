/*
 * The example computes the length of a list
 * by using a recursive function.
 */


#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};

int length(struct listNode* x)
/*@ rule <k> $ => return len(A); ...</k> <heap>... list(x)(A)  ...</heap>  */
{
  if (x == 0) return 0;
  else 
  {
    return (length(x->next) + 1);
  }
}

//@ var A : Seq
