// #include <stdio.h>
// #include <stdlib.h>		/* for malloc, NULL, size_t */
// #include <stdarg.h>		/* for va_ stuff */
// #include <string.h>		/* for strcat et al. */
#include "fsl.h"
 
void printargs(int arg1, ...) /* print all int type args, finishing with -1 */
{
  va_list ap;
  int i;
 
  va_start(ap, arg1); 
  for (i = arg1; i != -1; i = va_arg(ap, int))
    printf("%d, ", i);
  va_end(ap);
  putchar('\n');
}
 

char *vstrcat(const char *first, ...)
{
	size_t len;
	char *retbuf;
	va_list argp;
	char *p;

	if(first == NULL)
		return NULL;

	len = strlen(first);
	va_start(argp, first);

	while((p = va_arg(argp, char *)) != NULL)
		len += strlen(p);

	va_end(argp);
	retbuf = malloc(len + 1);	/* +1 for trailing \0 */

	if(retbuf == NULL)
		return NULL;		/* error */

	(void)strcpy(retbuf, first);
	va_start(argp, first);		/* restart; 2nd scan */

	while((p = va_arg(argp, char *)) != NULL)
		(void)strcat(retbuf, p);

	va_end(argp);
	return retbuf;
}

int testDifferent(int x, ...){
	va_list argp;
	va_start(argp, x);
	int y1 = va_arg(argp, int);
	int y2 = va_arg(argp, int);
	int y3 = va_arg(argp, int);
	long int y4 = va_arg(argp, long int);
	long long int y5 = va_arg(argp, long long int);
	double y6 = va_arg(argp, double);
	printf("%d, %d, %d, %d, %d, %f\n", y1, y2, y3, y4, y5, y6);
	va_end(argp);
	return 0;
}
 

int main(void) {
	printargs(5, 2, 14, 84, 97, 15, 24, 48, -1);
	printargs(84, 51, -1);
	printargs(-1);
	printargs(1, -1);

	char *str = vstrcat("Hello, ", "world!", "1", "23", "456", "789", (char *)NULL);
	puts(str);
	
	char mychar = 5;
	short int myshort = 10;
	float myfloat = 30.0;
	
	testDifferent(0, mychar, myshort, (int)15, (long int)20L, (long long int)25LL, myfloat);

	return 0;
}