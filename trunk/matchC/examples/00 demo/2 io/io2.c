#include <stdlib.h>
#include <stdio.h>


struct listNode {
  int val;
  struct listNode *next;
};


void read_write(int n)
{
  while (n) {
    int t;

    scanf("%d", &t);
    printf("%d ", t);
    n -= 1;
  }
}

void read_write_buffer(int n)
{
  int i;
  struct listNode *x;

  i = 0;
  x = 0;
  while (i < n) {
    struct listNode *y;

    y = x;
    x = (struct listNode*) malloc(sizeof(struct listNode));
    scanf("%d", &(x->val));
    x->next = y;
    i += 1;
  }

  while (x) {
    struct listNode *y;

    y = x->next;
    printf("%d ",x->val);
    free(x);
    x = y;
  }
}


int main()
{
  int n;

  //@ assume <in> [5, 1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10] </in> <out> . </out>

  scanf("%d", &n);
  read_write(n);
  //@ assert <in> [5, 6, 7, 8, 9, 10] </in> <out> [1, 2, 3, 4, 5] </out>

  scanf("%d", &n);
  read_write_buffer(n);
  //@ assert <in> . </in> <out> [1, 2, 3, 4, 5, 10, 9, 8, 7, 6] </out>
}
