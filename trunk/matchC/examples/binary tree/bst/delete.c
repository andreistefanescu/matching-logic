#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


int find_min(struct treeNode *t)
/*@ rule <k> $ => return m; ...</k> <heap>... tree(t)(T) ...</heap>
    if ~(t = 0) /\ isBst(T) /\ in(m, tree2mset(T)) /\ leq({m}, tree2mset(T)) */
{
  if (t->left == NULL)
    return t->val;
  else
    return find_min(t->left);
}


struct treeNode* bst_delete(struct treeNode *t, int v)
/*@ rule <k> $ => return ?t; ...</k>
         <heap>... tree(t)(T) => tree(?t)(?T) ...</heap>
    if isBst(T) /\ isBst(?T) /\ tree2mset(?T) = diff(tree2mset(T), {v}) */
{
  int min;

  if (t == NULL)
    return NULL;

  if (v == t->val) {
    if (t->left == NULL) {
      struct treeNode *tmp;

      tmp = t->right;
      free(t);

      return tmp;
    }
    else if (t->right == NULL) {
      struct treeNode *tmp;

      tmp = t->left;
      free(t);

      return tmp;
    }
    else {
      min = find_min(t->right);
      t->right = bst_delete(t->right, min);
      t->val = min;
    }
  }
  else if (v < t->val)
    t->left = bst_delete(t->left, v);
  else
    t->right = bst_delete(t->right, v);

  return t;
}


//@ var m : Int
//@ var T : Tree

