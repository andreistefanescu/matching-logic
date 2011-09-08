/*
 * Function computing the length of a double linked list.
 */


#include <stdlib.h>
#include <stdio.h>


struct dllistNode {
  int val;
  struct dllistNode *prev;
  struct dllistNode *next;
};


int length(struct dllistNode* a)
/*@ rule <k> $ => return len(A); ...</k>
         <heap>... dllist(a)(A) ...</heap> */
{
  int l;
  l = 0;

  if (a != 0) {
    /*@ inv <heap>... dllseg(old(a),a)(?A1), dllist(a)(?A2) ...</heap>
            /\ l = len(?A1) /\ A = ?A1 @ ?A2 */  
    while (a != 0) {
      a = a->next ;
      l = l + 1 ;
    }
  }
  return l;
}


//@ var A : Seq
