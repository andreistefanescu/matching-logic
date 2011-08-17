#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


int bst_find(struct treeNode *t, int v)
/*@ rule <k> $ => return r; <_/k> <heap_> tree(t)(T) <_/heap>
    if isBst(T)
       /\ (~(r = 0) /\ in(v, tree2mset(T)) \/ r = 0 /\ ~in(v, tree2mset(T))) */
{
  if (t == NULL)
    return 0;
  else if (v == t->val)
    return 1;
  else if (v < t->val)
    return bst_find(t->left, v);
  else
    return bst_find(t->right, v);
}


//@ var r : Int
//@ var T : Tree

