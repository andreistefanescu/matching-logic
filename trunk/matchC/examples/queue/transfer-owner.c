/*
 * Function transfers the first element of the src queue
 * to the end of the dest queue.
 */


#include <stdlib.h>
#include <stdio.h>

struct listNode {
int val;
struct listNode *next;
};

struct queueNode {
struct listNode* head;
struct listNode* tail;
};


struct queueNode* transfer(struct queueNode *dest, struct queueNode* src)
/*@ rule <k> $ => return dest; ...</k>
         <heap>... queue(dest)(A), queue(src)([val] @ B)
                   =>
                   queue(dest)(A @ [val]), queue(src)(B)
         ...</heap>
 */
{
  struct listNode* n;
  
  if (src != 0)
  {
    if (dest != 0)
    {
      if(src->head != 0)
      {
        n = src->head;
        if(src->head == src->tail)
        {
          src->head = 0;
          src->tail = 0;
        }
        else
        {
          src->head = n->next;
        }
        if(dest->head !=0)
        {
          dest->tail->next = n;
        }
        else
        {
          dest->head = n;
        }
        dest->tail = n;
      }
    }
  }
  return dest;
}


//@ var A, B : Seq
//@ var val : Int
