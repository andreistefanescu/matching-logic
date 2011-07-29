#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* reverse(struct listNode *x)
/*@ rule <k> $ => return p1; </k>
         <heap_> list(x)(A) => list(p1)(rev(A)) <_/heap> */
{
  struct listNode *p;

  p = NULL;
  //@ inv <heap_> list(p)(?B), list(x)(?C) <_/heap> /\ A = rev(?B) @ ?C
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }

  return p;
}

int main() {}

//@ var A, B, C : Seq

