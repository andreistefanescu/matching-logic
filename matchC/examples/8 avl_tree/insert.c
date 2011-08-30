/*
 * Function max returns the maximum value between two integer values.
 *
 * Function new_leaf creates a new node and returns the address to it.
 *
 * Function height returns the height of the tree.
 *
 * Function update_height computes the height of a tree.
 *
 * Function left_rotate transforms the right child node of the root into the 
 * new root.
 * 
 * Function right_rotate transforms the left child node of the root into the 
 * new root.
 *
 * Function balance rotates the tree received ar argument so that it becomes an
 * avl tree.
 *
 * Function avl_insert adds a new node of value "value" into the avl tree and
 * maintains the properties of the tree.
 */


#include<stdlib.h>


struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};


int max(int a, int b)
//@ rule <k> $ => return maxInt(a, b); ...</k>
{
  return a > b ? a : b;
}


struct node* new_leaf(int value)
{
  struct node *leaf;
  leaf = (struct node *) malloc(sizeof(struct node));

  leaf->value = value;
  leaf->height = 1;
  leaf->left = NULL;
  leaf->right = NULL;

  return leaf;
}


int height(struct node *tree)
/*@ rule <k> $ => return height(T); ...</k> <heap>... htree(tree)(T) ...</heap>
    if hasHeight(T) */
{
  return tree ? tree->height : 0;
}

void update_height(struct node *tree)
{
  tree->height = max(height(tree->left), height(tree->right)) + 1;
}


struct node* left_rotate(struct node *x)
{
  struct node *y;

  y = x->right;
  x->right = y->left;
  y->left = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node* right_rotate(struct node *x)
{
  struct node *y;

  y = x->left;
  x->left = y->right;
  y->right = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node* balance(struct node *tree)
{
  if (height(tree->left) - height(tree->right) > 1) {
    if (height(tree->left->left) < height(tree->left->right))
      tree->left = left_rotate(tree->left);
    tree = right_rotate(tree);
  }
  else if (height(tree->left) - height(tree->right) < -1) {
    if (height(tree->right->left) > height(tree->right->right))
      tree->right = right_rotate(tree->right);
    tree = left_rotate(tree);
  }

  return tree;
}


struct node* avl_insert(struct node *tree, int value)
/*@ rule <k> $ => return ?tree; ...</k>
         <heap>... htree(tree)(T) => htree(?tree)(?T) ...</heap>
    if isAvl(T) /\ isAvl(?T)
       /\ tree2mset(st(?T)) = tree2mset(st(T)) U {value}
       /\ 0 <= height(?T) - height(T) /\ height(?T) - height(T) <= 1 */
{
  if (tree == NULL)
    return new_leaf(value);

  tree->value;
  if (value < tree->value)
    tree->left = avl_insert(tree->left, value);
  else
    tree->right = avl_insert(tree->right, value);

  update_height(tree);
  tree = balance(tree);

  return tree;
}


//@ var m : Int
//@ var T : Tree

