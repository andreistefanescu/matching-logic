/*
 * The example computes the minimum between two values
 */

#include <stdio.h>

int maximum(int x, int y)
//@ rule <k> $ => return minInt(x, y); ...</k>
{
  if (x < y) {
    return x;
  }
  else {
    return y;
  }	
}
