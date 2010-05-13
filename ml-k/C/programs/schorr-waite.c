#include "fsl.h"

int counter = 0;

typedef struct struct_node {
	unsigned int m:1, c:1, v:1; /* booleans */
	struct struct_node *l, *r;
	int value;
} * node;

void schorr_waite(node root) {
	node t = root; 
	node p = NULL;
	while (p != NULL || (t != NULL && ! t->m)) {
		if (t == NULL || t->m) {
			if (p->c) { /* pop */
				node q = t; 
				t = p; 
				p = p->r; 
				t->r = q;
			} else { /* swing */
				node q = t; 
				t = p->r; 
				p->r = p->l; 
				p->l = q; 
				p->c = 1;
			}
		} else { /* push */
			node q = p; 
			p = t; 
			t = t->l; 
			p->l = q; 
			p->m = 1; 
			p->c = 0; 
		}
	}
}
	
node createNode(){
	printf("creating new node %d\n", counter);
	node newNode = (node)malloc(sizeof(struct struct_node));
	newNode->c = 0;
	newNode->m = 0;
	newNode->v = 0;
	newNode->l = NULL;
	newNode->r = NULL;
	newNode->value = counter;
	counter++;
	return newNode;
}
node setLeft(node curr, node left){
	printf("Setting left child of %d to %d\n", curr->value, left->value);
	curr->l = left;
	return left;
}

// algorithm  dft(x) 
   // visit(x) 
   // FOR each y such that (x,y) is an edge DO 
     // IF y was not visited yet THEN 
        // dft(y)
		
void showGraph(node this){
	
}

int main(void) {
	node root = createNode();
	setLeft(root, createNode());

}
