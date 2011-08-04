#include<stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* list_filter(struct listNode* x, int v)
/*@ rule <k> $ => return ?x; <_/k>
         <heap_> list(x)(A) => list(?x)(filter(v, A)) <_/heap> */
{
	struct listNode* y;
  
  /*@ inv <heap> list(x)(?A) <_/heap>
          /\ v = !v /\ filter(v, A) = filter(v, ?A) */ 
	while (x != NULL && x->val == v) {
	  struct listNode* z;

		z = x->next;
		free(x);
		x = z;
	}

  if (x == NULL)
    return NULL;

	y = x;
  /*@ inv <heap> lseg(x, y)(?B), y |-> [?v, ?n], list(?n)(?C) <_/heap>
          /\ v = !v /\ filter(v, A) = ?B @ [?v] @ filter(v, ?C) */
	while(y->next != NULL) {
	  struct listNode* z;

    z = y->next;
		if(z->val == v) {
			y->next = z->next;
			free(z);
		}
		else
			y = z;
	}

	return x;
}


/*@ var n : Int */
/*@ var A, B, C : Seq */

