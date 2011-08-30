/*
 * WE CURRENTLY DO NOT SUPPORT "&"
 *
 * The following program is undefined in C, because it accesses the
 * location corresponding to a dangling pointer.  gcc compiles it with
 * no complains and the resulting binary program runs fine.
 */

#include <stdio.h>

int main() {
  int *p;
  // If you comment the next block, the resulting program compiles with gcc
  // but the resulting binary yields a segmentation fault when executed.
  // Normally, the program would be undefined before the memory access *p
  // because of reading the uninitialized variable p, but gcc does not check it.
  { int x; p = &x; }
  printf("%d", *p);
}
