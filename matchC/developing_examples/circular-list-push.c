/*
 * Function that adds an new node of value val to a circular singly linked list.
 */


#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* clpush(struct listNode* x, int val)
/*@ rule <k> $ => return x; ...</k>
         <heap>... x |-> [v, n], lseg(n, x)(A) =>
                   x |-> [v, ?aux], lseg(?aux,x)([val] @ A) ...</heap>
 */
{
  struct listNode* aux;
  aux = (struct listNode*)malloc(sizeof(struct listNode));
  aux->val = val;
  aux->next = x->next;
  x->next = aux;
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
  printf("%d %d\n", x->val, y->val);
  x = clpush(x,9);
  printf("%d %d %d\n", x->val, x->next->val, x->next->next->val);
  return 0;
}

//@ var aux, n, v : Int
//@ var A : Seq
