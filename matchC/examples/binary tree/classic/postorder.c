#include <stdio.h>
#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


void tree_postorder(struct treeNode *t)
/*@ rule <k> $ => return; ...</k> <heap>... tree(t)(T) ...</heap>
         <out>... . => tree2postorder(T) </out> */
{
  if (t == NULL)
    return;

  tree_postorder(t->left);
  tree_postorder(t->right);
  printf("%d ", t->val);
}


//@ var T : Tree

