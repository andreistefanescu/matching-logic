#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* merge_sort(struct listNode* x)
/*@ rule <k> $ => return ?x; <_/k> <heap_> list(x)(A) => list(?x)(?A) <_/heap>
    if isSorted(?A) /\ seq2mset(A) = seq2mset(?A) */
{
  struct listNode* p;
  struct listNode* y;
  struct listNode* z;

  if (x == NULL || x->next == NULL)
    return x;

  y = NULL;
  z = NULL;
  /*@ inv <heap_> list(x)(?A), list(y)(?B), list(z)(?C) <_/heap>
          /\ seq2mset(A) = seq2mset(?A) U seq2mset(?B) U seq2mset(?C)
          /\ (len(?B) = len(?C) \/ len(?B) = len(?C) + 1 /\ x = 0) */
          ///\ (x = old(x) \/ ~(y = 0) /\ ~(z = 0)) */
  while (x != NULL) {
    struct listNode* t;

    t = x;
    x = x->next;
    t->next = y;
    y = t;

    if (x != NULL) {
      t = x;
      x = x->next;
      t->next = z;
      z = t;
    }
  }

  y = merge_sort(y);
  z = merge_sort(z);

  if (y->val < z->val) {
    x = p = y;
    y = y->next;
  }
  else {
    x = p = z;
    z = z->next;
  }
  /*@ inv <heap_>
            lseg(x, p)(?A1), p |-> [?v, ?n], list(y)(?B), list(z)(?C)
          <_/heap>
          /\ seq2mset(A) = seq2mset(?A1 @ [?v]) U seq2mset(?B) U seq2mset(?C)
          /\ leq(seq2mset(?A1 @ [?v]), seq2mset(?B))
          /\ leq(seq2mset(?A1 @ [?v]), seq2mset(?C))
          /\ isSorted(?A1 @ [?v]) /\ isSorted(?B) /\ isSorted(?C) */
  while (y != NULL && z != NULL) {
    if (y->val < z->val) {
      p->next = y;
      y = y->next;
    }
    else {
      p->next = z;
      z = z->next;
    }
		
    p = p->next;
  }
	
  if (y != NULL)
    p->next = y;
  else
    p->next = z;
	
  return x;
}

int main() {}

//@ var v, n : Int
//@ var A, B, C : Seq

