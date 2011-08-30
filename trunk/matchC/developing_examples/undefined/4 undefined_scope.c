/*
 * The following program is undefined in C, because it accesses the
 * location corresponding to a dangling pointer.  gcc compiles it with
 * no complains and the resulting binary program runs fine.
 */

#include <stdio.h>

int main() {
  int *p;
  // If you comment the next block, the resulting program compiles but segfaults
  { int x; p = &x; }
  printf("%d", *p);
}

