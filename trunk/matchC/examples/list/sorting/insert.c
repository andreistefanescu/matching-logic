#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* list_insert(struct listNode* x, int v)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A) => list(?x)(?A) ...</heap>
    if isSorted(A) /\ isSorted(?A) /\ seq2mset(?A) = seq2mset(A) U {v} */
{
  struct listNode* n;
  struct listNode* y;

  n = (struct listNode *) malloc(sizeof(struct listNode));
  n->val = v;
  n->next = NULL;

  if (x == NULL)
    return n;

  if (x->val >= v) {
    n->next = x;

    return n;
  }

  y = x;
  /*@ inv <heap>...
            lseg(x, y)(?B), y |-> [?v, ?n], list(?n)(?C), n |-> [v, 0]
          ...</heap>
          /\ v = !v /\ A = ?B @ [?v] @ ?C /\ ?v < v */
  while (y->next != NULL && y->next->val < v)
    y = y->next;

  n->next = y->next;
  y->next = n;

  return x;
}


//@ var A, B, C : Seq
