/*
 * Function computing the maximum value between two
 * natural numbers.
 */

#include <stdio.h>

int maximum(int x, int y)
//@ rule <k> $ => return maxInt(x, y); ...</k>
{
  if (x < y) {
    return y;
  }
  else {
    return x;
  }
}
