#include "fsl.h"
int* f(int x[]);

// typedef struct str {
	// int (*funcArr[2])(void);
	// int (*funcArr2D[2][2])(void);
// } strdef ;

// typedef struct that {
	// struct str this;
// } thatdef ;


int main(void){
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
	d2[0][0] = 5;
	d3[0][0][0] = 5;
	
	funcArr[0] = main;
	funcArr2D[0][0] = main;
	funArrofArr[0] = f;
	
	// thatdef t;
	// t.this.funcArr[0] = funcArr[0];
	return 0;
}

int* f(int x[]){
	return NULL;
}
