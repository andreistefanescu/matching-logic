/*
 * Function computing recursively the multiplication of two
 * natural numbers by repeated additions.
 */

#include <stdio.h>

int multiplication_by_add(int x, int y)
//@ rule <k> $ => return (x * y); ...</k>
{
  if (x == 0) {
    return 0;
  }
  else if (x < 0)
  {
    return -multiplication_by_add(-x,y);
  }
  else if (x > 0)
  {
    return y + multiplication_by_add(x - 1, y);
  }
}
