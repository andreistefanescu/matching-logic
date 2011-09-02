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
                   x |-> [v, ?n], lseg(?n,x)([val] @ A) ...</heap>
 */
{
  struct listNode* aux;
  aux = (struct listNode*)malloc(sizeof(struct listNode));
  aux->val = val;
  aux->next = x->next;
  x->next = aux;
  return x;
}

//@ var n, v : Int
//@ var A : Seq
