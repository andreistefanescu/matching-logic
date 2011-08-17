#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


struct listNode* list_reverse(struct listNode *x)
/*@ rule <k> $ => return ?p; ...</k>
         <heap>... list(x)(A) => list(?p)(rev(A)) ...</heap> */
{
  struct listNode *p;

  p = NULL;
  //@ inv <heap>... list(p)(?B), list(x)(?C) ...</heap> /\ A = rev(?B) @ ?C
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    x->next = p;
    p = x;
    x = y;
  }

  return p;
}

struct listNode* list_append(struct listNode *x, struct listNode *y)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A), list(y)(B) => list(?x)(A @ B) ...</heap> */
{
  struct listNode *p;
  if (x == NULL)
    return y;

  p = x;
  /*@ inv <heap>... lseg(x, p)(?A1), list(p)(?A2) ...</heap> 
          /\ A = ?A1 @ ?A2 /\ ~(p = 0) */
  while (p->next != NULL)
    p = p->next;
  p->next = y;

  return x;
}


struct listNode* list_create(int n)
{
  struct listNode *x;

  x = NULL;
  while (n) {
    struct listNode *y;

    y = x;
    x = (struct listNode*) malloc(sizeof(struct listNode));
    x->val = n;
    x->next = y;

    n -= 1;
  }

  return x;
}


void list_print(struct listNode* x)
/*@ rule <k> $ => return; ...</k> <heap>... list(x)(A) ...</heap>
         <out>... epsilon => A </out> */
{
  /*@ inv <heap>... lseg(old(x), x)(?A1), list(x)(?A2) ...</heap>
          <out>... ?A1 </out>
          /\ A = ?A1 @ ?A2 */
  while(x != NULL) {
    printf("%d ", x->val);
    x = x->next;
  }
  printf("\n"); 
}

void list_free(struct listNode* x)
//@ rule <k> $ => return; ...</k> <heap>... list(x)(A) => . ...</heap>
{
  //@ inv <heap>... list(x)(?A) ...</heap>
  while(x != NULL) {
    struct listNode *y;

    y = x->next;
    free(x);
    x = y;
  }
}


int main()
{
  struct listNode *x;
  struct listNode *y;

  x = list_create(5);
  //@ assert <heap> list(x)([1, 2, 3, 4, 5]) </heap>
  x = list_reverse(x);
  //@ assert <heap> list(x)([5, 4, 3, 2, 1]) </heap>
  list_free(x);
  //@ assert <heap> . </heap>
  x = list_create(5);
  printf("x: ");
  list_print(x);
  //@ assert <heap> list(x)(A1) </heap> <out> A1 </out>
  x = list_reverse(x);
  printf("reverse(x): ");
  list_print(x);
  //@ assert <heap> list(x)(rev(A1)) </heap> <out> A1 @ rev(A1) </out>
  list_free(x);
  //@ assert <heap> . </heap>

  x = list_create(3);
  //@ assert <heap> list(x)([1, 2, 3]) </heap>
  y = list_create(3);
  //@ assert <heap> list(x)([1, 2, 3]), list(y)([1, 2, 3]) </heap>
  x = list_append(x, y);
  //@ assert <heap> list(x)([1, 2, 3, 1, 2, 3]) </heap>
  list_free(x);
  //@ assert <heap> . </heap>
  x = list_create(3);
  printf("x: ");
  list_print(x);
  //@ assert <heap> list(x)(A2) </heap>
  y = list_create(3);
  printf("y: ");
  list_print(y);
  //@ assert <heap> list(x)(A2), list(y)(A3) </heap>
  x = list_append(x, y);
  printf("append(x, y): ");
  list_print(x);
  /*@ assert <heap> list(x)(A2 @ A3) </heap>
             <out> A1 @ rev(A1) @ A2 @ A3 @ A2 @ A3 </out> */
  list_free(x);
  //@ assert <heap> . </heap>
}


//@ var A, B, C : Seq

