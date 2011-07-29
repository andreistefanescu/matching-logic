#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* insert(struct listNode* x, int v)
/*@ pre < config > < env > x |-> ?x i |-> ?i </ env > < heap > list(?x)(A) </ heap > < form > TrueFormula </ form > </ config > */
/*@ post < config > < env > ?rho </ env > < heap > list(?x)(?A) </ heap > < form > returns ?x /\ (seq2mset(?A) === seq2mset(A @ [?i])) </ form > </ config > */
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
  /*@ inv */
	while (y->next != NULL && y->next->value < v) {
    y = y->next;
	}
  n->next = y->next;
  y->next = n;

	return x;
}

int main() {}

/*@ var ?x ?y ?it ?i ?in ?aux ?v1 ?v2 ?p : ?Int */
/*@ var ?A ?B ?C ?D : ?Seq */
/*@ var A : FreeSeq */
/*@ var ?rho ?H : ?MapItem */

