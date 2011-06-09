#include <stdio.h>


void trusted(int n);
void untrusted(int n);
void any(int n);


void trusted(int n)
{
  printf("%d ", n);
  untrusted(n);
  any(n);
  if (n)
    trusted(n - 1);
}


void untrusted(int n)
{
  printf("%d ", -n);
  if (n)
    any(n - 1);
}


void any(int n)
{
  untrusted(n); // violates security policy
  if(n > 10)
    trusted(n - 1);
}


int main()
{
  trusted(5);
  any(5);
}

