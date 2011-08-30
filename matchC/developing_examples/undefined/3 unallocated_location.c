/*
 * The program below accesses a location which has not been assocated.
 * gcc compiles it, but the generated binary yields a segmentation fault.
 */


#include <stdio.h>


int main()
{
  int *x;
  printf("%d", *x);
}
