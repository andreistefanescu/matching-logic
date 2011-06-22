#include<stdio.h>
#include<stdlib.h>


struct node {
  int value;
  int height;
  struct node *left;
  struct node *right;
};


int max(int a, int b)
{
  return a > b ? a : b;
}

struct node * new_leaf(int value)
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
/* rule <k> $ => return height(T) <_/k> <heap_> btree(tree)(T) <_/heap>
    if */
{
  return tree ? tree->height : 0;
}

int update_height(struct node *tree)
{
  tree->height = max(height(tree->left), height(tree->right)) + 1;
}

int find_min(struct node *tree)
{
  // assert(tree != NULL);

  if (tree->left == NULL)
    return tree->value;
  else
    return find_min(tree->left);
}

struct node * left_rotate(struct node *x)
{
  // assert(x->right != NULL);
  struct node *y;

  y = x->right;
  x->right = y->left;
  y->left = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node * right_rotate(struct node *x)
{
  // assert(x->left != NULL);
  struct node *y;

  y = x->left;
  x->left = y->right;
  y->right = x;

  update_height(x); 
  update_height(y); 

  return y;
}

struct node * balance(struct node *tree)
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

struct node * insert(struct node *tree, int value)
/*@ rule <k> $ => return tree1; <_/k>
         <heap_> htree(tree)(T) => htree(tree1)(T1) <_/heap>
    if isAvl(T) /\ isAvl(T1)
       /\ tree2mset(st(T1)) = tree2mset(st(T)) U {value}
       /\ 0 <= height(T1) - height(T) /\ height(T1) - height(T) <= 1 */
{
  if (tree == NULL)
    return new_leaf(value);

  if (value < tree->value)
    tree->left = insert(tree->left, value);
  else
    tree->right = insert(tree->right, value);

  update_height(tree);
  tree = balance(tree);

  return tree;
}

struct node * delete(struct node *tree, int value)
{
  int min;

  if (tree == NULL)
    return NULL;

  if (value == tree->value) {
    if (tree->left == NULL)
      return tree->right;
    else if (tree->right == NULL)
      return tree->left;
    else {
      min = find_min(tree->right);
      tree->right = delete(tree->right, min);
      tree->value = min;
    }
  }
  else if (value < tree->value)
    tree->left = delete(tree->left, value);
  else
    tree->right = delete(tree->right, value);

  update_height(tree);
  tree = balance(tree);

  return tree;
}

/*
void check_balance(struct node *tree)
{
  if (tree == NULL)
    return;

  check_balance(tree->left);
  check_balance(tree->right);

  // assert(tree->height == max(height(tree->left), height(tree->right)) + 1);
  // assert(fabs(height(tree->left) - height(tree->right)) < 2);
}
*/

void print_tree(struct node *tree, int indent) {
  int i;

  if (tree == NULL)
    return;

  /*
  print_tree(tree->right, indent + 1);
  for(i = 0; i < indent; i++) printf("  ");
  printf("(%d, %d)\n", tree->value, tree->height);
  print_tree(tree->left, indent + 1);
  */
  print_tree(tree->left, indent + 1);
  printf("%d ", tree->value);
  printf("%d\n", tree->height);
  print_tree(tree->right, indent + 1);
}

int main() {
  int i;
  int n;
  struct node *tree;

  return 0;

  i = 0;
  n = 16;
  tree = NULL;
  while(i < n) {
    tree = insert(tree, i);
    i += 1;
  }

  print_tree(tree, 0);
}

//@ var T : Tree

/*
  int n, value;
  struct node *tree

  tree = NULL;
  scanf("%d", &n);
  while(n--) {
    scanf("%d", &value);
    printf("insert %d\n", value);
    tree = insert(tree, value);
    check_balance(tree);
  }

  print_tree(tree, 0);

*/

