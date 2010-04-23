#include "fsl.h"

int* listCons(int* p, int n);
int* mergesort(int* p);
int main() {
	int* head = NULL;
	
	head = listCons(head, 20);	
	head = listCons(head, 25);
	head = listCons(head, 15);
	head = listCons(head, 30);
	head = listCons(head, 10);
	head = listCons(head, 35);
	
	// for (int i = 0; i < 1000; i++){
		// head = listCons(head, i);
		// head = listCons(head, 1000-i);
	// }
	
	head = mergesort(head);
	int* curr = head;
	while (curr != NULL){
		printf("%d,", *curr);
		curr = *(curr + 1);
	}
	return 0;
}

int* listCons(int* p, int n){
	int* next = malloc(2);
	*next = n;
	*(next + 1) = p;
	return next;
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
