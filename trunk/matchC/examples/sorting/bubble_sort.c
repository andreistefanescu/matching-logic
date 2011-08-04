#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* bubble_sort(struct listNode* x)
/*@ rule <k> $ => return ?x; <_/k> <heap_> list(x)(A) => list(?x)(?A) <_/heap>
    if isSorted(?A) /\ seq2mset(A) = seq2mset(?A) */
{
  int change;

  if (x == NULL || x->next == NULL)
    return x;

  change = 1 ;
  /*@ inv <heap_> list(x)(?A) <_/heap> /\ ~(x = 0) /\ seq2mset(A) = seq2mset(?A)
          /\ (isSorted(?A) \/ ~(change = 0)) */
  while (change) {
    struct listNode* y;

    change = 0;
    y = x;
    /*@ inv <heap_> lseg(x, y)(?B), y |-> [?v, ?n], list(?n)(?C) <_/heap>
            /\ ~(x = 0) /\ seq2mset(A) = seq2mset(?B @ [?v] @ ?C)
            /\ (isSorted(?B @ [?v]) \/ ~(change = 0)) */
    while (y->next != NULL) {
      if (y->val > y->next->val) {
        int tmp;

        change = 1;
        tmp = y->val;
        y->val = y->next->val;
        y->next->val = tmp;
      }
      y = y->next;
    }
  }

  return x;
}


//@ var v, n : Int
//@ var A, B, C, D : Seq

