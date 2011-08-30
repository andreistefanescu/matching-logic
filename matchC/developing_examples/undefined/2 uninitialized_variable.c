/*
 * The program below performs a read on an uninitialized integer variable,
 * which is undefined according to the C standard.
 * gcc happily compiles this program and the resulting program prints 0.
 */


#include <stdio.h>


int main()
{
  int x;
  printf("%d", x);
}
