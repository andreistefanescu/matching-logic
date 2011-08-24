/*
 * The example prefixes a node to an existing list.
 * The value filed of the new node is taken from
 * the second argument of the list.
 */


#include <stdlib.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* prefix(struct listNode* x, int i)
/*@ rule <k> $ => return ?x; ...</k> <heap>... list(x)(A) => list(?x)([i] @ A) ...</heap> */
{
  struct listNode* y;
  y = (struct listNode*) malloc (sizeof(struct listNode));
  y->val = i;
  y->next = x;
  x = y;
  return x;
}

//@ var A : Seq

