#include <stdio.h>
struct tiny {
  char c;
  char d;
  char e;
};

void f (int n, struct tiny x, struct tiny y, struct tiny z, long l) {
  if (x.c != 10)
    printf("BUG: 10\n");
  if (x.d != 20)
    printf("BUG: 20\n");
  if (x.e != 30)
    printf("BUG: 30\n");

  if (y.c != 11)
    printf("BUG: 11\n");
  if (y.d != 21)
    printf("BUG: 21\n");
  if (y.e != 31)
    printf("BUG: 31\n");

  if (z.c != 12)
    printf("BUG: 12\n");
  if (z.d != 22)
    printf("BUG: 22\n");
  if (z.e != 32)
    printf("BUG: 33\n");

  if (l != 123)
    printf("BUG: 123\n");
}

int main (void) {
  struct tiny x[3];
  x[0].c = 10;
  x[1].c = 11;
  x[2].c = 12;
  x[0].d = 20;
  x[1].d = 21;
  x[2].d = 22;
  x[0].e = 30;
  x[1].e = 31;
  x[2].e = 32;
  f (3, x[0], x[1], x[2], (long) 123);
  return 0;
}

