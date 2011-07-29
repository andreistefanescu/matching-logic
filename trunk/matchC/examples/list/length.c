#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

int list_length(struct listNode* x)
//@ rule <k> $ => return len(A); </k> <heap_> list(x)(A) <_/heap>
{
  int l;
  
  l = 0;
  /*@ inv <heap_> lseg(old(x), x)(?A1), list(x)(?A2) <_/heap> 
          /\ A = ?A1 @ ?A2 /\ l = len(?A1) */
  while (x != NULL) {
    l += 1;
    x = x->next;
  }

  return l;
}

int main() {}

//@ var A : Seq

