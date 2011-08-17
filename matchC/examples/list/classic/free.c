#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


void list_free(struct listNode* x)
//@ rule <k> $ => return; ...</k> <heap>... list(x)(A) => . ...</heap>
{
  //@ inv <heap>... list(x)(?A) ...</heap>
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    free(x);
    x = y;
  }
}


//@ var A : Seq

