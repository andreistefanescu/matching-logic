#include "fsl.h"

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
	
	return x;
}
