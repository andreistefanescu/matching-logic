#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


void read_write(int n)
/*@ rule <k> $ => return; ...</k> <in> A => . ...</in> <out>... . => A </out>
    if n = len(A) */
{
  /*@ inv <in> ?B ...</in> <out>... ?A </out>
          /\ n >= 0 /\ len(?B) = n /\ A = ?A @ ?B */
  while (n) {
    int t;

    scanf("%d", &t);
    printf("%d ", t);
    n -= 1;
  }
}


//@ var A, B : Seq

