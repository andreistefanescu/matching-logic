/*
 * Function avl_find goes through the nodes of an avl tree based on their values
 * and returns whether or not the value was found.
 */


#include<stdlib.h>


struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};


int avl_find(struct node *tree, int value)
/*@ rule <k> $ => return r; ...</k> <heap>... htree(tree)(T) ...</heap>
    if isAvl(T) /\ (~(r = 0) /\ in(value, tree2mset(st(T)))
       \/ r = 0 /\ ~in(value, tree2mset(st(T)))) */
{
  if (tree == NULL)
    return 0;
  else if (value == tree->value)
    return 1;
  else if (value < tree->value)
    return avl_find(tree->left, value);
  else
    return avl_find(tree->right, value);
}


//@ var r : Int
//@ var T : Tree

