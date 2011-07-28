#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


struct treeNode *newNode(int v)
{
  struct treeNode *node;
  node = (struct treeNode *)malloc(sizeof(struct treeNode));
  node->val = v;
  node->left = node->right = 0;
  return node;
}


struct treeNode *insertRecursive(struct treeNode *t, int v)
/*@ rule <k> $ => return ?t; <_/k>
         <heap_> tree(t)(T) => tree(?t)(?T) <_/heap>
    if isBst(T) /\ isBst(?T) /\ tree2mset(?T) = tree2mset(T) U {v} */
{
  if (t == 0)
    return newNode(v);

  if (v < t->val)
    t->left = insertRecursive(t->left, v);
  else
    t->right = insertRecursive(t->right, v);

  return t;
}


struct treeNode *insertIterative(struct treeNode *root, int v)
{
  struct treeNode *t;
  struct treeNode *p;

  if (root == 0)
    return newNode(v);

  p = 0;
  t = root;

  /* rule <heap_> tree(t)(T) => tree(old(t))(?T) <_/heap>
      if isBst(T) /\ isBst(?T) /\ tree2mset(?T) = tree2mset(T) U {v} */
  {
    while (t != 0) {
      p = t;
      if (v < t->val)
        t = t->left;
      else
        t = t->right;
    }

    if (v < p->val)
      p->left = newNode(v);
    else
      p->right = newNode(v);
  }

  return root;
}


struct treeNode *findRecursive(struct treeNode *t, int v)
/* rule <k> $ => return ?r; <_/k> <heap_> tree(t)(T) <_/heap>
    if isBst(T) /\ (~(?r = 0) /\ in(v0, tree2mset(T))
        \/ ?r = 0 /\ ~(in(v0, tree2mset(T)))) */
{
  if (t == 0)
    return 0;
  else if (v == t->val)
    return 1;
  else if (v < t->val)
    return findRecursive(t->left, v);
  else
    return findRecursive(t->right, v);
}


struct treeNode *deleteRecursive(struct treeNode *t, int v)
{
  if (t == 0)
    return 0;
  else if (v == t->val)
    return 1;
  else if (v < t->val)
    return findRecursive(t->left, v);
  else
    return findRecursive(t->right, v);
}


int main()
{
  return 0;
}


//@ var r : Int
//@ var T : Tree

