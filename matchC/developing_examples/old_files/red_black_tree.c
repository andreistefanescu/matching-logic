struct red_black_tree
{
  int value;
  int color;
  struct red_black_tree *left;
  struct red_black_tree *right;
  struct red_black_tree *parent;
};


struct red_black_tree *left_rotate(struct red_blac_tree *x)
{
  struct red_black_tree *y;

  y = x->right;
  x->right = y->left;
  if (y->left != NULL)
    y->left->parent = x;
  y->parent = x->parent;
  if (x->parent != NULL)
    if (x == x->parent->left)
      x->parent->left = y;
    else
      x->parent->right = y;
  y->left = x;
  x->parent = y;

  return y;
}

struct red_black_tree *left_rotate(struct red_blac_tree *x)
{
  struct red_black_tree *y;

  y = x->left;
  x->left = y->right;
  if (y->right != NULL)
    y->right->parent = x;
  y->parent = x->parent;
  if (x->parent != NULL)
    if (x == x->parent->right)
      x->parent->right = y;
    else
      x->parent->left = y;
  y->right = x;
  x->parent = y;

  return x;
}

struct red_black_tree * insert(struct red_blac_tree * tree, int value)
{


}



int main()
{
  return 0;
}
