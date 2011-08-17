#include <stdio.h>
#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


void print(struct listNode* x)
/*@ rule <k> $ => return; </k> <heap_> list(x)(A) <_/heap>
         <out_> epsilon => A </out> */
{
  /*@ inv <heap_> lseg(old(x), x)(?A1), list(x)(?A2) <_/heap> <out_> ?A1 </out>
          /\ A = ?A1 @ ?A2 */
  while(x != NULL) {
    printf("%d ", x->val);
    x = x->next;
  }
  printf("\n"); 
}


//@ var A : Seq

