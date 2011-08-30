/*
 * The program below accesses uninitialized memory, so it is undefined.
 * gcc compiles it and the generated program executes fine.
 */


#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


int main()
{
  struct listNode *x;

  x = (struct listNode*) malloc(sizeof(struct listNode));
  printf("%p\n", x->next);
}
