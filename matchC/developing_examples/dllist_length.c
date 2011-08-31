/*
 * Function computing the length of a double linked list.
 */


#include <stdlib.h>
#include <stdio.h>

struct dllistNode {
  int val;
  struct dllistNode *next;
  struct dllistNode *prev;
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
    /*@ inv <heap>... dllseg(0,a)(?y,x,?A1), dllseg(?y,x)(?z,0,?A2) ...</heap>
          /\ l = len(?A1) */  
    while (x != 0) {
      x = x->next ;
      l = l + 1 ;
    }
  }
  return l;
}

int main()
{
  struct dllistNode* x;
  x = (struct dllistNode*)malloc(sizeof(struct dllistNode));
  x->val = 5;
  x->next = 0;
  x->prev = 0;
  printf("%d\n", length(x));
  return 0;
}

//@ var y, z : Int
//@ var A : Seq
