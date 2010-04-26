#include "fsl.h"
//#include <stdio.h>

struct bigstruct {
	int a;
	int b;
	int c;
	int* p;
	int d;
	int e;
	int f;
	struct bigstruct* this;
} ;

int main(void){
	int x = 1;
	int* p = &x;
	int** pp = &p;
	int* ap[] = {p, p};
	int** app = ap;
	int data[] = {1, 0};
	x++; // x == 2
	(*p)++; // x == 3
	(**pp)++; // x == 4;
	//int* q = ap[1];
	(**(ap + data[0]))++; // x == 5;
	(*(ap[data[1]]))++; // x == 6;
	
	struct bigstruct s;
	struct bigstruct* ps = &s;
	s.a = 1;
	s.b = 2;
	s.c = 3;
	s.d = 4;
	s.e = 5;
	s.f = 6;
	s.p = &(s.b);
	s.this = &s;
	x += *((s.this)->p); // x == 8;
	x += s.b + s.e + s.f; // x == 21;
	(*((s.this)->p)) ++; // s.b == 3;
	x += (&s)->b; // x == 24
	
	printf("%d\n",x);
	return x;
}
