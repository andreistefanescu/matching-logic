#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* clenque(struct listNode* x, int value)
/* rule <k> $ => return x; ...</k>
         <heap>... (lseg(x, n)([v]), lseg(n,x)(A)) =>
                   (lseg(x, n)([value] @ [v]), lseg(n,x)(A)) ...</heap>
 */
{
  struct listNode* aux;

  aux = (struct listNode*)malloc(sizeof(struct listNode));
  aux->val = x->val;
  aux->next = x->next;
  x->val = value;
  x->next = aux;
  //@ assert <heap>... lseg(x,aux)([value]), lseg(aux,n)([v]) ...</heap>
  //@ assert <heap>... lseg(x,n)([value] @ [v]) ...</heap>
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
