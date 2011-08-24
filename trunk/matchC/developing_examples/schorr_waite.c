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

  if (root != NULL)
    root->mark;

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

  if (q != NULL)
    q->mark;
}


void schorr_waite_graph(struct graphNode *root)
/* rule <k> $ => return; ...</k>
         <heap>... swgraph(root, empty)(G) => swgraph(root, empty)(?G) ...</heap>
    if isConst(0, proj(1, G)) /\ isConst(3, proj(1, ?G))
       /\ proj(0, T) = proj(0, ?T) */
{
  struct graphNode *p;
  struct graphNode *q;

  if (root != NULL)
    root->mark;

  p = root; q = NULL;
  /* inv <heap>... swtree(p)(?TP), swtree(q)(?TQ) ...</heap>
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

  if (q != NULL)
    q->mark;
}


//@ var T, TP, TQ : Tree

/*
eq Schorr-Waite-tree =
    assume [cleanTree(root) ** rest1] ;
    t = root ;
    p = null ;
    inv (t == null && [stackTree(p) ** rest]) || (* t == 1 &&& [markedTree(t) ** stackTree(p) ** rest]) || (* t == 0 &&& [cleanTree(t) ** stackTree(p) ** rest])
    while (p != null || (t != null && * t == 0)) do (
      if (t == null || * t == 1) then (
        if (*(p + 1) == 1) then (  --- POP
          q = t ;                  --- q = t
          t = p ;                  --- t = p
          p = *(p + 3) ;           --- p = p -> right
          *(t + 3) = q ;           --- t -> right = q
        )
        else (                     --- SWING
          q = t ;                  --- q = t
          t = *(p + 3) ;           --- t = p -> right
          *(p + 3) = *(p + 2) ;    --- p -> right = p -> left
          *(p + 2) = q ;           --- p -> left = q
          *(p + 1) = 1 ;           --- p -> c = 1
        )
      )
      else (                       --- PUSH
        q = p ;                    --- q = p
        p = t ;                    --- p = t
        t = *(t + 2) ;             --- t = t -> left
        *(p + 2) = q ;             --- p -> left = q
        * p = 1 ;                  --- p -> m = 1
        *(p + 1) = 0 ;             --- p -> c = 0
      )
    ) ;
    assert [markedTree(t) ** rest1]
.


eq Schorr-Waite-graph =
    assume [cleanGraph(nodes,emptySet)(root)] ;
    t = root ;
    p = null ;
    inv t == null && [stackInGraph(nodes1,emptySet)(p) ** rest] && nodes1 == nodes
        || t != null &&
           (* t == 1 &&& [markedGraph(nodes1,out1)(t) ** stackInGraph(nodes2,out2)(p) ** rest] ||
            * t == 0 &&& [ cleanGraph(nodes1,out1)(t) ** stackInGraph(nodes2,out2)(p) ** rest])
            && nodes == nodes1 UNION nodes2 && out1 in nodes2 && out2 in nodes1
    while (p != null || (t != null && * t == 0)) do (
      if (t == null || * t == 1) then (
        if (*(p + 1) == 1) then (  --- POP
          q = t ;                  --- q = t
          t = p ;                  --- t = p
          p = *(p + 3) ;           --- p = p -> right
          *(t + 3) = q ;           --- t -> right = q
        )
        else (                     --- SWING
          q = t ;                  --- q = t
          t = *(p + 3) ;           --- t = p -> right
          *(p + 3) = *(p + 2) ;    --- p -> right = p -> left
          *(p + 2) = q ;           --- p -> left = q
          *(p + 1) = 1 ;           --- p -> c = 1
        )
      )
      else (                       --- PUSH
        q = p ;                    --- q = p
        p = t ;                    --- p = t
        t = *(t + 2) ;             --- t = t -> left
        *(p + 2) = q ;             --- p -> left = q
        * p = 1 ;                  --- p -> m = 1
        *(p + 1) = 0 ;             --- p -> c = 0
      )
    ) ;
    assert [markedGraph(nodes3,emptySet)(t)] && nodes3 == nodes
.
*/

