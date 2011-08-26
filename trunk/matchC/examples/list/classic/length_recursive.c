/*
 * Function computing recursively the length of a list.
 */

#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


int length(struct listNode* x)
//@ rule <k> $ => return len(A); ...</k> <heap>... list(x)(A) ...</heap>
{
  if (x == 0) return 0;
  return length(x->next) + 1;  
}

//@ var A : Seq
