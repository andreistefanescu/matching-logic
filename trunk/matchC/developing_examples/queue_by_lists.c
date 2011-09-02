/*
 * Simulation of functions enqueue and dequeue using just singly linked lists.
 */


#include <stdlib.h>
#include <stdio.h>

struct listNode {
  int val;
  struct listNode *next;
};

struct listNode* enqueue(struct listNode* x, int value)
/*@ rule <k> $ => return ?newnode; ...</k>
         <heap>... list(x)(A) => list(?newnode)([value] @ A) ...</heap>
 */      
{
  struct listNode* newnode;
  newnode = (struct listNode*)malloc(sizeof(struct listNode));
  newnode->val = value;
  newnode->next = 0; 
  if(x == 0) return newnode;
  newnode->next = x;
  return newnode;
}

struct listNode* dequeue(struct listNode* x)
/*@ rule <k> $ => return ?x; ...</k>
         <heap>... list(x)(A @ [v]) => list(?x)(A) ...</heap>
 */
{
  struct listNode* last;
  struct listNode* prelast;

  if(x->next == 0) {
    free(x);
    return 0;
  }
  else {
    last = x->next;
    prelast = x;
    /*@ inv <heap>... lseg(x,prelast)(?A1), 
                      prelast |-> [?vp, last], 
                      last |-> [?vl, ?n],
                      list(?n)(?A2) ...</heap>
            /\ A @ [v] = ?A1 @ [?vp] @ [?vl] @ ?A2
    */
    while(last->next != 0) {
      prelast = last;
      last = last->next;
    }
    prelast->next = 0;
    free(last);
    return x;
  }
}


//@ var v, vp, vl, n : Int
//@ var A : Seq
