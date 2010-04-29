#include "fsl.h"
int* f(int x[]);

// // typedef struct str {
	// // int (*funcArr[2])(void);
	// // int (*funcArr2D[2][2])(void);
// // } strdef ;

// // typedef struct that {
	// // struct str this;
// // } thatdef ;

// struct point {
	// int x;
	// int y;
// } ;
// struct s1 {
	// struct point a[2];
// } ;

// struct s2 {
	// struct s1 a;
	// struct s1 b;
// } ;


int main(void){
	int retval = 0;
	int w;
	int* x = &w;
	*x = 5;
	int** y = &x;
	int z = **y;
	int d1[2];
	int d2[2][2];
	int d3[2][2][2];
	
	int (*funcpt)(void) = main;
	// need function pointer around array type
	// function pointers inside something
	
	int (*funcArr[2])(void);
	int (*funcArr2D[2][2])(void);
	int* (*funArrofArr[2])(int x[]);
	
	d1[0] = 5;
	// d2[0][0] = 5;
	// d3[0][0][0] = 5;
	
	funcArr[0] = main;
	// funcArr2D[0][0] = main;
	// funArrofArr[0] = f;
	
	// struct s1 mys1;
	// struct s2 mys2;
	// mys1.a[0].x = 5;
	// mys1.a[0].y = -5;
	// mys1.a[1].x = 10;
	// mys1.a[1].y = -10;
	// mys2.a = mys1;
	// mys2.b = mys1;
	
	// retval += mys2.a.a[0].x + mys2.a.a[1].y;
	
	// thatdef t;
	// t.this.funcArr[0] = funcArr[0];
	return retval;
}

int* f(int x[]){
	return NULL;
}
