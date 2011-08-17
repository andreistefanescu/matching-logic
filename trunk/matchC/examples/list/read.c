#include <stdio.h>
#include <stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode *readList(int n)
/*@ rule <k> $ => return ?x; </k> <heap_> . => list(?x)(A) <_/heap>
         <in> A => epsilon <_/in>
    if n = len(A) */
{
  int i;
  struct listNode *x;
  struct listNode *p;

  if (n == 0)
    return NULL;

  x = (struct listNode*) malloc(sizeof(struct listNode));
  scanf("%d", &(x->val));
  x->next = NULL;

  i = 1;
  p = x;
  /*@ inv <heap_> lseg(x, p)(?B), p |-> [?v, 0] <_/heap> <in> ?C <_/in>
          /\ i <= n /\ len(?C) = n - i /\ A = ?B @ [?v] @ ?C */
  while (i < n) {
    p->next = (struct listNode*) malloc(sizeof(struct listNode));
    p = p->next;
    scanf("%d", &(p->val));
    p->next = NULL;
    i += 1;
  }

  return x;
}


//@ var v : Int
//@ var A, B, C : Seq

