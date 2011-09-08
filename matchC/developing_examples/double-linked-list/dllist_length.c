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
  struct dllistNode* x;
  l = 0;
  if (a != 0) {             
    x = a;
    /*@ inv <heap>... dllseg(a,x)(?A1), dllist(x)(?A2) ...</heap>
            /\ l = len(?A1) /\ A = ?A1 @ ?A2 */  
    while (x != 0) {
      x = x->next ;
      l = l + 1 ;
    }
  }
  return l;
}

//@ var y, z : Int
//@ var A : Seq
