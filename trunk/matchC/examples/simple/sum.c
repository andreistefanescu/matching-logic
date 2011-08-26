/*
 * Function computing the sum for the first n natural
 * numbers.
 */


#include <stdio.h>


int sum(int n)
/*@ rule <k> $ => return (n * (n + 1)) / 2; ...</k>
    if n >= 0 */
{
  int s;

  s = 0;
  //@ inv s = ((old(n) - n) * (old(n) + n + 1)) / 2 /\ n >= 0
  while (n > 0) {
    s += n;
    n -= 1;
  }

  return s;
}

