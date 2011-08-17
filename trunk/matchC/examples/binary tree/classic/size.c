#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


int tree_size(struct treeNode *t)
//@ rule <k> $ => return size(tree2mset(T)); </k> <heap_> tree(t)(T) <_/heap>
{
  if (t == NULL)
    return 0;
  else
    return 1 + tree_size(t->left) + tree_size(t->right);
}


//@ var T : Tree

