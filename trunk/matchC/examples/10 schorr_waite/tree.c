/*
 * 
 */
#include<stdlib.h>


struct graphNode {
  int mark;
  struct graphNode *left;
  struct graphNode *right;
};


void schorr_waite_tree(struct graphNode *root)
/*@ rule <k> $ => return; ...</k>
         <heap>... swtree(root)(T) => swtree(root)(?T) ...</heap>
    if isConst(0, marks(T)) /\ isConst(3, marks(?T))
       /\ pointers(T) = pointers(?T) */
{
  struct graphNode *p;
  struct graphNode *q;

  if (root == NULL)
    return;

  p = root; q = NULL;
  /*@ inv <heap>... swtree(p)(?TP), swtree(q)(?TQ) ...</heap>
          /\ isMarked(marks(?TP), marks(?TQ))
          /\ pointers(T) = restore(?TP, ?TQ) */
  while (p != NULL) {
    struct graphNode *t;

    p->mark = p->mark + 1;
    if (p->mark == 3 || p->left != NULL && p->left->mark == 0) {
      // parallel assignment p->left, p->right, q, p = p->right, q, p, p->left
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = p;
      p = t;
    }
    else {
      // parallel assignment p->left, p->right, q = p->right, q, p->left
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = t;
    }
  }
}


//@ var T, TP, TQ : Tree

