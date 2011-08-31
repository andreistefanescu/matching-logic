/*
 * Function that inserts a new node with value v into a binary search tree.
 */


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


struct treeNode* insert(int v, struct treeNode *t)
/*@ rule <k> $ => return ?t; ...</k>
         <heap>... tree(t)(T) => tree(?t)(?T) ...</heap>
    if isBst(T) /\ isBst(?T) /\ tree2mset(?T) = tree2mset(T) U {v} */
{
  if (t == NULL)
    return newNode(v);

  if (v < t->val)
    t->left = insert(v, t->left);
  else
    t->right = insert(v, t->right);

  return t;
}


//@ var T : Tree
