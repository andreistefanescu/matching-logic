/*
 * Function that appends the content of one queue - src, to another and frees
 * the memory allocated to the src queue.
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


struct queueNode* steal(struct queueNode *dest, struct queueNode* src)
/*@ rule <k> $ => return dest; ...</k>
         <heap>... queue(dest)(A), queue(src)(B)
                => queue(dest)(A @ B) ...</heap>
 */
{
  if (src != 0) {
    if (dest != 0) {
      if (src->head != 0) {
        if(dest->head != 0) {
          dest->tail->next = src->head;
        }
        else {
          dest->head = src->head;
        }
        dest->tail = src->tail;
      }
      free(src);
    }
  }
  return dest;
}

//@ var A, B : Seq
