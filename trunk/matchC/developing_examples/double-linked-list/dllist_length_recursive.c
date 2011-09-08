/*
 * Function computing recursively the length of a double linked list.
 */


#include <stdlib.h>
#include <stdio.h>


struct dllistNode {
  int val;
  struct dllistNode *prev;
  struct dllistNode *next;
};


int length_recursive(struct dllistNode* a)
/*@ rule <k> $ => return len(A); ...</k>
         <heap>... dllist(a)(A) ...</heap> */
{
  if (a == 0) return 0;
  return 1 + length(a->next);
}


//@ var A : Seq
