/*
 * 
 */
#include<stdlib.h>


struct graphNode {
  int mark;
  struct graphNode *left;
  struct graphNode *right;
};


void schorr_waite_graph(struct graphNode *root)
/*@ rule <k> $ => return; ...</k>
         <heap>...
           swgraph({root}s, {0}s)(G) => swgraph({root}s, {0}s)(?G)
         ...</heap>
    if isConst(0, marks(G)) /\ pointers(G) = pointers(?G) */
    // /\ isConst(3, marks(?G)) */
{
  struct graphNode *p;
  struct graphNode *q;

  if (root == NULL)
    return;

  p = root; q = NULL;
  /*@ inv <heap>... swgraph({p, q}s, {0}s)(?GPQ) ...</heap>
          /\ root = !root /\ isRestorable(p, q, root, ?GPQ)
          /\ pointers(G) = pointers(restore(p, q, ?GPQ))
          */
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
      // breakpoint
      t = p->left;
      p->left = p->right;
      p->right = q;
      q = t;
      // breakpoint
    }
  }

}


//@ var T, TP, TQ : Tree
//@ var G, GPQ : Graph

/*
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

