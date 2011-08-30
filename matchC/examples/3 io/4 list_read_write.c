/*
 * Function list_read_write reads n elements from the standard input and
 * writes them to the standard output in reverse order.  To do so, it
 * first stores the n elements in a singly-linked list, which it allocates
 * as the elements are read, and then it outputs the n elements from the
 * list, at the same time dealocating the list.  In the end, the heap
 * stays unchanged (the heap does not appear in the function specification).
 */


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

