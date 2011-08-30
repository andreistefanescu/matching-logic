#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


void tree_inorder(struct treeNode *t)
/*@ rule <k> $ => return; ...</k> <heap>... tree(t)(T) ...</heap>
         <out>... . => tree2list(T) </out> */
{
  if (t == NULL)
    return;

  tree_inorder(t->left);
  printf("%d ", t->val);
  tree_inorder(t->right);
}


//@ var T : Tree

