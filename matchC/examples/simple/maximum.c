/*
 * The example computes the maximum between two values
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