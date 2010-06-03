#include <stdio.h>
#include <stdlib.h>

struct list_el {
   int val;
   struct list_el * next;
};

typedef struct list_el item;

item* listReverseUnchecked(item* p);
item* listReverse(item* p);
item* listAppend(item* p, int n);
int listSum(item* p);

int main(void){
	item* head = (item*)malloc(sizeof(item));
	head->val = 20; 
	head->next = NULL;
	
	listAppend(head, 25);
	listAppend(head, 15);
	listAppend(head, 30);
	listAppend(head, 10);
	listAppend(head, 35);
	
	item* curr = head;
	while (curr != NULL){
		printf("%d,", curr->val);
		curr = curr->next;
	}
	printf("\n");
	
	int sum1 = listSum(head);
	int first = head->val;
	head = listReverse(head);
	curr = head;
	while (curr != NULL){
		printf("%d,", curr->val);
		curr = curr->next;
	}
	printf("\n");	
	int last = head->val;
	int sum2 = listSum(head);
	return (sum1 - sum2) + (last - first); // should be 15
}

item* listAppend(item* p, int n){
	item* x;

    if (p != NULL) {
        x = p;
        while (x->next != NULL) {
            x = x->next;
        }		
		item* next = (item*)malloc(sizeof(item));
        x->next = next;
		next->val = n;
		next->next = NULL;
    }
	return p;
}

int listSum(item* p){
	int sum = 0;
	item* x;
    if (p != NULL) {
        x = p;
		sum += x->val;
        while (x->next != NULL) {
            x = x->next;
			sum += x->val;
        }		
	}
	return sum;
}

item* listReverse(item* p){
    if (p != NULL) {
		item* x = p->next;
        p->next = NULL;
        while(x != NULL) {
            item* tmp = x->next;
            x->next = p;
            p = x;
            x = tmp;
        }
    }
	return p;
}

