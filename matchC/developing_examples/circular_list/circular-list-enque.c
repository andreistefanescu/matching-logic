#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* clenque(struct listNode* x, int val)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... (x |-> [v, n], lseg(n,x)(A)) =>
                  (?x |-> [val,n], lseg(n,?x)(A @ [v])) ...</heap>
 */
{
  struct listNode* aux;
  aux = (struct listNode*)malloc(sizeof(struct listNode));
  aux->val = val;
  aux->next = x->next;
  x->next = aux;
  x = x->next;
  return x;
}


int main()
{
  struct listNode *x;
  struct listNode *y;
  x = (struct listNode*)malloc(sizeof(struct listNode));
  x->val = 5;
  x->next = 0;
  y = (struct listNode*)malloc(sizeof(struct listNode));
  y->val = 8;
  y->next = x;
  x->next = y;
  x = clenque(x,9);
  return 0;
}

//@ var A : Seq
//@ var v, n : Int
