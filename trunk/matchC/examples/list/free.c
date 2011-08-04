#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

void list_free(struct listNode* x)
//@ rule <k> $ => return; </k> <heap_> list(x)(A) => . <_/heap>
{
  //@ inv <heap_> list(x)(?A) <_/heap>
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    free(x);
    x = y;
  }
}


//@ var A : Seq

