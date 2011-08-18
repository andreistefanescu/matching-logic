#include <stdlib.h>
#include <stdio.h>


struct treeNode {
  int val;
  struct treeNode *left;
  struct treeNode *right;
};

struct listNode {
  int val;
  struct listNode *next;
};

struct stackNode {
  struct treeNode *val;
  struct stackNode *next;
};


struct listNode* tree_to_list_recursive(struct treeNode *t, struct listNode *l)
/*@ rule <k> $ => return ?l; ...</k>
         <heap>...
           tree(t)(T), list(l)(A) => list(?l)(tree2list(T) @ A)
         ...</heap>
         <out>... . => rev(tree2list(T)) </out> */
{
  struct listNode *ln;

  if (t == NULL)
    return l;

  ln = (struct listNode *) malloc(sizeof(struct listNode));
  ln->val = t->val;
  ln->next = tree_to_list_recursive(t->right, l);
  printf("%d ", t->val);
  l = tree_to_list_recursive(t->left, ln);
  free(t);

  return l;
}

struct listNode* tree_to_list_iterative(struct treeNode *t)
/*@ rule <k> $ => return ?l; ...</k>
         <heap>... tree(t)(T) => list(?l)(tree2list(T)) ...</heap>
         <out>... . => rev(tree2list(T)) </out> */
{
  struct listNode *l;
  struct stackNode *s;

  if (t == NULL)
    return NULL;

  l = NULL;
  s = (struct stackNode *) malloc(sizeof(struct stackNode));
  s->val = t;
  s->next = NULL;
  /*@ inv <heap>... treeList(s)(?TS), list(l)(?A) ...</heap>
          <out>... rev(?A) </out>
          /\ tree2list(T) = treeList2list(rev(?TS)) @ ?A */
  while (s != NULL) {
    struct treeNode *tn;
    struct listNode *ln;
    struct stackNode *sn;

    sn = s;
    s = s->next ;
    tn = sn->val;
    free(sn) ;
    if (tn->left != NULL) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn->left;
      sn->next = s;
      s = sn;
    }
    if (tn->right != NULL) {
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn;
      sn->next = s;
      s = sn;
      sn = (struct stackNode *) malloc(sizeof(struct stackNode));
      sn->val = tn->right;
      sn->next = s;
      s = sn;
      tn->left = tn->right = NULL;
    }
    else {
      ln = (struct listNode *) malloc(sizeof(struct listNode));
      ln->val = tn->val;
      ln->next = l;
      l = ln;
      printf("%d ", ln->val);
      free(tn);
    }
  }

  return l;
}


struct treeNode* create()
{
  struct treeNode* root;

  root = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->val = 4;
  root->left = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->left->val = 2;
  root->left->left = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->left->left->val = 1;
  root->left->left->left = 0;
  root->left->left->right = 0;
  root->left->right = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->left->right->val = 3;
  root->left->right->left = 0;
  root->left->right->right = 0;
  root->right = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->right->val = 6;
  root->right->left = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->right->left->val = 5;
  root->right->left->left = 0;
  root->right->left->right = 0;
  root->right->right = (struct treeNode*) malloc(sizeof(struct treeNode));
  root->right->right->val = 7;
  root->right->right->left = 0;
  root->right->right->right = 0;

  return root;
}

void destroy(struct listNode* x)
{
  struct listNode *y;

  while(x) {
    y = x->next;
    free(x);
    x = y;
  }
}


int main()
{
  struct treeNode* t;
  struct listNode* l;

  t = create();
  //@ assert <heap> tree(t)(T1) </heap>
  l = tree_to_list_recursive(t, 0);
  /*@ assert <heap> list(l)(tree2list(T1)) </heap>
             <out> rev(tree2list(T1)) </out> */
  destroy(l);
  //@ assert <heap> . </heap>

  t = create();
  //@ assert <heap> tree(t)(T2) </heap>
  l = tree_to_list_iterative(t);
  /*@ assert <heap> list(l)(tree2list(T2)) </heap>
             <out> rev(tree2list(T1)) @ rev(tree2list(T2)) </out> */
  destroy(l);
  //@ assert <heap> . </heap>
}


//@ var A, TS : Seq
//@ var T : Tree

