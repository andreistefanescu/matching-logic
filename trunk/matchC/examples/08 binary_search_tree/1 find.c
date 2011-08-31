/*
 * Function that searches a binary search tree for a node with value "v".
 */


#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


int find(struct treeNode *t, int v)
/*@ rule <k> $ => return r; ...</k> <heap>... tree(t)(T) ...</heap>
    if isBst(T)
       /\ (~(r = 0) /\ in(v, tree2mset(T)) \/ r = 0 /\ ~in(v, tree2mset(T))) */
{
  if (t == NULL) return 0;
  if (v == t->val) return 1;
  if (v < t->val) return find(t->left, v);
  return find(t->right, v);
}


//@ var r : Int
//@ var T : Tree

