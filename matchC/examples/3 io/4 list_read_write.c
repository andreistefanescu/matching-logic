#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


void list_read_write(int n)
/*@ rule <k> $ => return; ...</k> <in> A => . ...</in> 
         <out>... . => rev(A) </out>
    if n = len(A) */
{
  int i;
  struct listNode *x;

  i = 0;
  x = 0;
  /*@ inv <in> ?B ...</in> <heap>... list(x)(?A) ...</heap>
          /\ i <= n /\ len(?B) = n - i /\ A = rev(?A) @ ?B */
  while (i < n) {
    struct listNode *y;

    y = x;
    x = (struct listNode*) malloc(sizeof(struct listNode));
    scanf("%d", &(x->val));
    x->next = y;
    i += 1;
  }

  /*@ inv <out>... ?A </out> <heap>... list(x)(?B) ...</heap>
          /\ A = rev(?A @ ?B) */
  while (x) {
    struct listNode *y;

    y = x->next;
    printf("%d ",x->val);
    free(x);
    x = y;
  }
}


//@ var A, B : Seq

