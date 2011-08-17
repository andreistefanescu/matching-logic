#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode *list_copy(struct listNode *x)
/*@ rule <k> $ => return ?y; <_/k>
         <heap_> list(x)(A), (. => list(?y)(A)) <_/heap> */
{
  struct listNode *y;
  struct listNode *iterx;
  struct listNode *itery;

  if (x == NULL)
    return NULL;

  y = (struct listNode *) malloc(sizeof(struct listNode));
  y->val = x->val;
  y->next = NULL;

  iterx = x->next;
  itery = y;
  /*@ inv <heap_>
            lseg(old(x), iterx)(?B @ [?v]), list(iterx)(?C),
            lseg(y, itery)(?B), itery |-> [?v, 0]
          <_/heap>
          /\ A = ?B @ [?v] @ ?C */
  while(iterx) {
    struct listNode *node;

    node = (struct listNode *) malloc(sizeof(struct listNode));
    node->val = iterx->val;
    node->next = NULL;
    itery->next = node;
    iterx = iterx->next;
    itery = itery->next;
  }

  return y;
}


/*@ var v: Int */
/*@ var A, B, C : Seq */

