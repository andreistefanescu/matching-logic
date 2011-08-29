/*
 * Function that swaps the first two elements of a list.
 
 * The function specification states that the list must have at least two
 * elements in order for the function to be called.
 */


#include <stdlib.h>
#include <stdio.h>


struct nodeList {
  int val;
  struct nodeList *next;
};


struct nodeList* swap(struct nodeList* x)
/*@ rule <k> $ => return ?x; ...</k> 
         <heap>... list(x)([first, second] @ A) 
                => list(?x)([second, first] @ A) ...</heap>
 */
{
  struct nodeList* p;
  p = x;
  x = x->next;
  p->next = x->next;
  x->next = p;
  return x;
}

/*@ var first, second : Int */
/*@ var A : Seq */
