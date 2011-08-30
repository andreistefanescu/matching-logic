/*
 * Function f() can only be called directly or indirectly by function h().
 * In other words, the specification of f() states that h must be in the stack.
 * The functions g() and h() have no specifications, which means that there
 * is nothing to prove about them.  The function main() has no specification
 * either, but according to the C semantics it is called when the program
 * starts, so matchC verifies it by default.  Use "//@ skip" in front of a
 * function if you don't want it verified.
 */


#include <stdio.h>


void f()
/*@ rule <k> $ => return; ...</k> <stack> S </stack>
    if in(h,ids(S)) */
{
  // any code
}

void g()
{
  // any code
  f();
  // any code
}

void h()
{
  // any code
  g();
  // any code
}

int main()
{
  // any code
  h();
  // Verification fails if you uncomment the next call
  //g();
  h();
  // any code
}


//@ var S : ListItem

