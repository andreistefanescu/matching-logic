/*
 * Function prints in preorder a binary tree without altering its content.
 */


#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


void tree_preorder(struct treeNode *t)
/*@ rule <k> $ => return; ...</k> <heap>... tree(t)(T) ...</heap>
         <out>... . => tree2preorder(T) </out> */
{
  if (t == NULL)
    return;

  printf("%d ", t->val);
  tree_preorder(t->left);
  tree_preorder(t->right);
}


//@ var T : Tree

