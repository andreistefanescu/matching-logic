#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* list_append(struct listNode *x, struct listNode *y)
/*@ rule <k> $ => return x1; </k>
         <heap_> list(x)(A), list(y)(B) => list(x1)(A @ B) <_/heap> */
{
  struct listNode *p;
  if (x == NULL)
    return y;

  p = x;
  /*@ inv <heap_> lseg(x, p)(?A1), list(p)(?A2) <_/heap> 
          /\ A = ?A1 @ ?A2 /\ ~(p = 0) */
  while (p->next != NULL)
    p = p->next;
  p->next = y;

  return x;
}

int main() {}

//@ var A, B : Seq

