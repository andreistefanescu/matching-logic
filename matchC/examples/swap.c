#include<stdio.h>
#include<stdlib.h>

void swap(int *x, int *y)
//@ rule <heap_> x|->(a=>b), y|->(b=>a) <_/heap>
{
  int t;

  t = *x;
  *x = *y;
  *y = t;
}

int main() {}

//@ var a, b : Int
