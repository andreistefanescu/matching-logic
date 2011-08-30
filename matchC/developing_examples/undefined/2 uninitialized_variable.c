/*
 * The program below performs a division by zero, which is undefined.
 * gcc happily compiles this program and the resulting program prints 0.
 */


#include <stdio.h>


int main()
{
  int x;
  printf("%d", x);
}
