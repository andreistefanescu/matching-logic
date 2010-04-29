//#include <stddef.h>
//#include <stdlib.h>
#include "fsl.h"
int* listReverseUnchecked(int* p);
int* listReverse(int* p);
int* listAppend(int* p, int n);
int listSum(int* p);

int main(void){
	int* head = malloc(2);
	*head = 20; 
	*(head + 1) = NULL;
	
	listAppend(head, 25);
	listAppend(head, 15);
	listAppend(head, 30);
	listAppend(head, 10);
	listAppend(head, 35);
	
	int* curr = head;
	while (curr != NULL){
		printf("%d,", *curr);
		curr = *(curr + 1);
	}
	printf("\n");
	
	int sum1 = listSum(head);
	int first = *head;
	head = listReverse(head);
	curr = head;
	while (curr != NULL){
		printf("%d,", *curr);
		curr = *(curr + 1);
	}
	printf("\n");	
	int last = *head;
	int sum2 = listSum(head);
	return (sum1 - sum2) + (last - first); // should be 15
}

int* listAppend(int* p, int n){
	int* x;
    /*assume <config> <env> a |-> a0 ;; b |-> b0 ;; x |-> ?x </env>
                    <heap> list(a0)(A) ** list(b0)(B) </heap> <form> TrueFormula </form> </config> ;*/

    if (p != NULL) {
        x = p;
        /*invariant <config> <env> a |-> a0 ;; x |-> ?x ;; !E </env>
                           <heap> lseg(a0,?x)(?A) ** list(?x)(?X) ** !H </heap>
                           <form> ?A :: ?X === A /\ ~(?x === 0) </form> </config> ;*/
        while (*(x + 1) != NULL) {
            x = *(x + 1);
        }		
		int* next = malloc(2);
        *(x + 1) = next;
		*next = n;
		*(next + 1) = NULL;
    }
	return p;
    // else {
        // p = b ;
    // }
    /*assert <config> <env> a |-> ?a ;; b |-> b0 ;; x |-> ?x </env>
                    <heap> list(?a)(A :: B) </heap> <form> (~(a0 === 0) /\ (?a === a0)) \/ ((a0 === 0) /\ (?a === b0)) </form> </config> ;*/

}

int listSum(int* p){
	int sum = 0;
	int* x;
    if (p != NULL) {
        x = p;
		sum += *x;
        while (*(x + 1) != NULL) {
            x = *(x + 1);
			sum += *x;
        }		
	}
	return sum;
}

int* listReverse(int* p){
    if (p != NULL) {
		int* x = *(p + 1);
        *(p + 1) = NULL;
        while(x != NULL) {
            int* tmp = *(x + 1);
            *(x + 1) = p;
            p = x;
            x = tmp;
        }
    }
	return p;
}

