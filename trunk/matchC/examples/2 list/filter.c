/*
 * Function filter deletes the nodes of a singly linked list that hold 
 * the value "v".
 */


#include<stdlib.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* filter(struct listNode* x, int v)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A) => list(?x)(filter(v, A)) ...</heap> */
{
  struct listNode* y;
  
  /*@ inv <heap>... list(x)(?A) ...</heap>
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
  /*@ inv <heap>... lseg(x, y)(?B), y |-> [?v, ?n], list(?n)(?C) ...</heap>
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

