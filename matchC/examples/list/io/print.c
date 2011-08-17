#include <stdio.h>
#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


void list_print(struct listNode* x)
/*@ rule <k> $ => return; ...</k> <heap>... list(x)(A) ...</heap>
         <out>... epsilon => A </out> */
{
  /*@ inv <heap>... lseg(old(x), x)(?A1), list(x)(?A2) ...</heap>
          <out>... ?A1 </out>
          /\ A = ?A1 @ ?A2 */
  while(x != NULL) {
    printf("%d ", x->val);
    x = x->next;
  }
  printf("\n"); 
}


//@ var A : Seq

