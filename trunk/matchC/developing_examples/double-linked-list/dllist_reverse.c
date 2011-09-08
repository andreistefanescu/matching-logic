#include <stdlib.h>
#include <stdio.h>

struct dllistNode {
  int val;
  struct dllistNode *prev;
  struct dllistNode *next;
};

struct dllistNode* reverse(struct dllistNode* a)
/*@ rule <k> $ => return ?a; ...</k>
         <heap>... dllist(a)(A) => dllist(?a)(rev(A)) ...</heap> */
{
  struct dllistNode* p;
  struct dllistNode* aux;
  
  p = 0;
  
  if ((a->next == 0) && (a->prev == 0)) {
    p = a;
  }
  else {
    p = a;
    
    a = a->next;
    a->prev = 0;
    
    p->next = 0;
    p->prev = 0;
  /*@ inv <heap>... dllseg(old(a),a)(?A1), 
                    dllist(a)(?A2) ...</ heap >
          /\ A = rev(?A1) @ ?A2 */
    while(a!=0)
    {
      aux = a->next;
      a->next = p;
      a->prev = 0;
      p->prev = a;
      p = a;
      a = aux;
    }
  }
  return p;
}


//@ var y, z : Int
//@var A : Seq
