#include <stdlib.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};


struct treeNode *newNode(int v)
{
  struct treeNode *node;
  node = (struct treeNode *) malloc(sizeof(struct treeNode));
  node->val = v;
  node->left = node->right = NULL;
  return node;
}


int find_min(struct treeNode *t)
/*@ rule <k> $ => return m; <_/k> <heap_> tree(t)(T) <_/heap>
    if ~(t = 0) /\ isBst(T) /\ in(m, tree2mset(T)) /\ leq({m}, tree2mset(T)) */
{
  if (t->left == NULL)
    return t->val;
  else
    return find_min(t->left);
}


struct treeNode *insertRecursive(struct treeNode *t, int v)
/*@ rule <k> $ => return ?t; <_/k>
         <heap_> tree(t)(T) => tree(?t)(?T) <_/heap>
    if isBst(T) /\ isBst(?T) /\ tree2mset(?T) = tree2mset(T) U {v} */
{
  if (t == NULL)
    return newNode(v);

  if (v < t->val)
    t->left = insertRecursive(t->left, v);
  else
    t->right = insertRecursive(t->right, v);

  return t;
}

int findRecursive(struct treeNode *t, int v)
/*@ rule <k> $ => return r; <_/k> <heap_> tree(t)(T) <_/heap>
    if (~(r = 0) /\ in(v, tree2mset(T)) \/ r = 0 /\ ~(in(v, tree2mset(T))))
    /\ isBst(T) */
{
  if (t == NULL)
    return 0;
  else if (v == t->val)
    return 1;
  else if (v < t->val)
    return findRecursive(t->left, v);
  else
    return findRecursive(t->right, v);
}

struct treeNode *deleteRecursive(struct treeNode *t, int v)
/*@ rule <k> $ => return ?t; <_/k>
         <heap_> tree(t)(T) => tree(?t)(?T) <_/heap>
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
      t->right = deleteRecursive(t->right, min);
      t->val = min;
    }
  }
  else if (v < t->val)
    t->left = deleteRecursive(t->left, v);
  else
    t->right = deleteRecursive(t->right, v);

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

//@ var m, r : Int
//@ var T : Tree

