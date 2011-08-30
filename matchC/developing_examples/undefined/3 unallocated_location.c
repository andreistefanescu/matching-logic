/*
 * The program below accesses a location which has not been assocated.
 * gcc compiles it, but the generated binary yields a segmentation fault.
 */


#include <stdio.h>


int main()
{
  int *x;
  x = (int *) 1000;
  printf("%d", *x);
}
