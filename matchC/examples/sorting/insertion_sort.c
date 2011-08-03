#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* insertion_sort(struct listNode* x)
/*@ rule <k> $ => return ?x; <_/k> <heap_> list(x)(A) => list(?x)(?A) <_/heap>
    if isSorted(?A) /\ seq2mset(A) = seq2mset(?A) */
{
  struct listNode* y;

  y = NULL;
  /*@ inv <heap_> list(y)(?B), list(x)(?C) <_/heap>
          /\ isSorted(?B) /\ seq2mset(A) = seq2mset(?B) U seq2mset(?C) */
  while (x != NULL) {
    struct listNode* n;

    n = x;
    x = x->next;
    n->next = NULL;
    if (y != NULL) {
      if (y->val < n->val) {
        struct listNode* z;

        z = y;
        /*@ inv <heap_>
                  lseg(y, z)(?B), z |-> [?v, ?n], list(?n)(?C), n |-> [nval, 0]
                <_/heap>
                /\ B = ?B @ [?v] @ ?C /\ ?v < nval */
			  while (z->next != NULL && z->next->val < n->val)
					z = z->next;

				n->next = z->next;
				z->next = n;
			}
			else {
				n->next = y;
				y = n;
			}
		}
		else {
			y = n;
		}						  
	}

  return y;
}

int main() {}

//@ var v, nval : Int
//@ var A, B, C : Seq

