#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


struct treeNode* newNode(int v)
{
  struct treeNode *node;
  node = (struct treeNode *) malloc(sizeof(struct treeNode));
  node->val = v;
  node->left = node->right = NULL;
  return node;
}


struct treeNode* bst_insert(struct treeNode *t, int v)
/*@ rule <k> $ => return ?t; ...</k>
         <heap>... tree(t)(T) => tree(?t)(?T) ...</heap>
    if isBst(T) /\ isBst(?T) /\ tree2mset(?T) = tree2mset(T) U {v} */
{
  if (t == NULL)
    return newNode(v);

  if (v < t->val)
    t->left = bst_insert(t->left, v);
  else
    t->right = bst_insert(t->right, v);

  return t;
}


//@ var T : Tree

