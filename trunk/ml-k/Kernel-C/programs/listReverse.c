//#include <stddef.h>
//#include <stdlib.h>
int* listReverseUnchecked(int* p);
int* listReverse(int* p);
int* listAppend(int* p, int n);

int main(void){
	// int* head = malloc(2);
	// *head = 20; 
	// *(head + 1) = NULL;
	
	// listAppend(head, 25);
	// listAppend(head, 15);
	// listAppend(head, 30);
	// listAppend(head, 10);
	// listAppend(head, 35);
	
	return 0;
}

// int* listAppend(int* p, int n){
	// int* x;
    // /*assume <config> <env> a |-> a0 ;; b |-> b0 ;; x |-> ?x </env>
                    // <heap> list(a0)(A) ** list(b0)(B) </heap> <form> TrueFormula </form> </config> ;*/

    // if (p != NULL) {
        // x = p;
        // /*invariant <config> <env> a |-> a0 ;; x |-> ?x ;; !E </env>
                           // <heap> lseg(a0,?x)(?A) ** list(?x)(?X) ** !H </heap>
                           // <form> ?A :: ?X === A /\ ~(?x === 0) </form> </config> ;*/
        // while (*(x + 1) != 0) {
            // x = *(x + 1);
        // }		
		// // int* next = malloc(2);
        // // *(x + 1) = next;
		// // *next = n;
		// // *(next + 1) = NULL;
    // }
	// return p;
    // // else {
        // // p = b ;
    // // }
    // /*assert <config> <env> a |-> ?a ;; b |-> b0 ;; x |-> ?x </env>
                    // <heap> list(?a)(A :: B) </heap> <form> (~(a0 === 0) /\ (?a === a0)) \/ ((a0 === 0) /\ (?a === b0)) </form> </config> ;*/

// }

// int* listReverse(int* p){
	// /*assume <config> <env> p |-> ?p ;; x |-> ?x ;; y |-> ?y </env>
                    // <heap> list(?p)(A) </heap> <form> TrueFormula </form> </config> ;*/
    // int* x;
	// int* y;
	// if (p != 0) {
        // x = *(p + 1) ;
        // *(p + 1) = 0 ;
		// /* invariant <config> <env> p |-> ?p ;; x |-> ?x ;; y |-> ?y </env>
              // <heap> list(?p)(?B) ** list(?x)(?C) </heap> <form> rev(A) === rev(?C) :: ?B /\ ~(?p === 0)</form> </config> ;*/
        // while(x != 0) {
            // y = *(x + 1) ;
            // *(x + 1) = p ;
            // p = x ;
            // x = y ;
        // }
    // }
    // /*assert <config> <env> p |-> ?p ;; x |-> ?x ;; y |-> ?y </env>
                    // <heap> list(?p)(rev(A)) </heap> <form> TrueFormula </form> </config> ;*/
	// return p;
// }

// int* listReverseUnchecked(int* p){  
	// /*assume <config> <env> p |-> ?p ;; x |-> ?x ;; y |-> ?y </env>
                    // <heap> list(?p)(A) </heap> <form> ~(?p === 0) </form> </config> ;*/
	// int* x;
	// int* y;
	// x = *(p + 1) ;
    // *(p + 1) = 0 ;
    // /*invariant <config> <env> p |-> ?p ;; x |-> ?x ;; y |-> ?y </env>
                       // <heap> list(?p)(?B) ** list(?x)(?C) </heap>
                       // <form> rev(A) === rev(?C) :: ?B /\ ~(?p === 0)</form> </config> ;*/
    // while(x != 0) {
        // y = *(x + 1) ;
        // *(x + 1) = p ;
        // p = x ;
        // x = y ;
    // }
	// /*assert <config> <env> p |-> ?p ;; x |-> ?x ;; y |-> ?y </env>
                    // <heap> list(?p)(rev(A)) </heap> <form> ~(?p === 0) </form> </config> ;*/
	// return p;
// }

