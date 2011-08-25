/*
 * The example computes the integer average of
 * thee numbers received as arguments.
 */

#include <stdio.h>

int average(int x, int y, int z)
/*@ rule <k> $ => return (x + y + z) / 3; ...</k> */
{
  int sum;
  sum = x + y + z;
  return (sum / 3);
}
