#include<stdlib.h>


struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};


int bst_find(struct node *tree, int value)
/*@ rule <k> $ => return r; <_/k> <heap_> htree(tree)(T) <_/heap>
    if isAvl(T) /\ (~(r = 0) /\ in(value, tree2mset(st(T)))
       \/ r = 0 /\ ~in(value, tree2mset(st(T)))) */
{
  if (tree == NULL)
    return 0;
  else if (value == tree->value)
    return 1;
  else if (value < tree->value)
    return bst_find(tree->left, value);
  else
    return bst_find(tree->right, value);
}


//@ var r : Int
//@ var T : Tree

