/*
 * The example defines the function which computes the
 * multiplication of two numbers by repeated additions.
 * The function is recursive.
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
		return -1 * multiplication_by_add(-x,y);
	}
	else if (x > 0)
	{
		return y + multiplication_by_add(x - 1, y);
	}
}
