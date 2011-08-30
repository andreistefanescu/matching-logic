/*
 * Function mirrors the structure of a binary tree.
 */


#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


void tree_mirror(struct treeNode *t)
/*@ rule <k> $ => return; ...</k>
         <heap>... tree(t)(T) => tree(t)(mirror(T)) ...</heap> */
{
  struct treeNode *tmp;

  if (t == NULL)
    return;

  tmp = t->left;
  t->left = t->right;
  t->right = tmp;
  tree_mirror(t->left);
  tree_mirror(t->right);
}


//@ var T : Tree

