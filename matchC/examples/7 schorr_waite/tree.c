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
    if isConst(0, proj(1, T)) /\ isConst(3, proj(1, ?T))
       /\ proj(0, T) = proj(0, ?T) */
{
  struct graphNode *p;
  struct graphNode *q;

  if (root == NULL)
    return;

  p = root; q = NULL;
  /*@ inv <heap>... swtree(p)(?TP), swtree(q)(?TQ) ...</heap>
          /\ isSWMarkedPath(proj(1, ?TP), proj(1, ?TQ))
          /\ proj(0, T) = SWPath2ptrTree(?TP, ?TQ) */
  while (p != NULL) {
    struct graphNode *t;

    p->mark = p->mark + 1;
    if (p->mark == 3 || p->left != NULL && p->left->mark == 0) {
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = p;
      p = t;
    }
    else {
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = t;
    }
  }
}


//@ var T, TP, TQ : Tree

