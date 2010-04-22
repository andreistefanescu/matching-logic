#include "fsl.h"

int* listAppend(int* p, int n);
int* mergesort(int* p);
int main() {
	int* head = NULL;
	
	head = listAppend(head, 20);	
	head = listAppend(head, 25);
	head = listAppend(head, 15);
	head = listAppend(head, 30);
	head = listAppend(head, 10);
	head = listAppend(head, 35);
	
	head = mergesort(head);
	int* curr = head;
	while (curr != NULL){
		printf("%d,", *curr);
		curr = *(curr + 1);
	}
	return 0;
}

int* listAppend(int* p, int n){
	int* x;
	if (p == NULL){
		int* next = malloc(2);
		*next = n;
		*(next + 1) = NULL;
		return next;
	} else {
        x = p;
        while (*(x + 1) != NULL) {
            x = *(x + 1);
        }		
		int* next = malloc(2);
        *(x + 1) = next;
		*next = n;
		*(next + 1) = NULL;
    }
	return p;
}

int* mergesort(int* l) {
	int* a;
	int* b;
	int* e;
	int* t;
	int* h;
    if (l != NULL && *(l + 1)) {
        // split the list in two
        a = NULL ;
        b = NULL ;
        *((int*)*(l + 1)) = *((int*)*(l + 1)) ;
        while (l != NULL) {
            e = l ;
            l = * (e + 1) ;
            * (e + 1) = a ;
            a = e ;
            if (l != NULL) {
                e = l ;
                l = * (e + 1) ;
                * (e + 1) = b ;
                b = e ;
            }
        }

		// sort the first half
        a = mergesort(a);
        // sort the second half
		b = mergesort(b);
        // merge the two halves
        h = 0 ;
        t = 0 ;
        // little extra help to unfold the queue heap pattern
        // * a = * a ;
        // * b = * b ;
        while (a != 0 && b != 0) {
            if (* b > * a) {
                e = a ;
                a = *(a + 1) ;
            } else {
                e = b ;
                b = *(b + 1) ;
            }

            if (h != 0) {
                *(t + 1) = e ;
            } else {
                h = e ;
            }
            t = e ;
        }

        if (a != 0) {
            *(t + 1) = a ;
        } else {
            *(t + 1) = b ;
        }

        l = h ;
    }
	return l;
	
}
