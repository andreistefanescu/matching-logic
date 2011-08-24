/* 
 * The example computes the sum for the first n natural 
 * numbers recursively.
 */


#include <stdio.h>


int sum(int n)
/*@ rule <k> $ => return (n * (n + 1)) / 2; ...</k>
    if n >= 0 */
{
	if (n <= 0) {
		return 0;
	}
	else {
		return  n + sum(n-1);
	}
}