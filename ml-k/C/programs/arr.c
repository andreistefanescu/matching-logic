#include "fsl.h"
struct point {
	int x;
	int y;
};

#define OK { printf("OK\n"); }

int main(void){
	int arr[2][2] = {{1, 2}, {3, 4}};
	
	if ((int*)(&arr) != (int*)(arr)) {
		printf("&arr != arr\n");
	} else OK
	if ((int*)(&arr[0]) != (int*)(arr)) {
		printf("&arr[0] != arr\n");
	} else OK
	if ((int*)(&*(arr + 0)) != (int*)(arr)) {
		printf("&*(arr + 0) != arr\n");
	} else OK
	if ((int*)((arr + 0)) != (int*)(arr)) {
		printf("arr + 0 != arr\n");
	} else OK
	if ((int*)(&(*(*(arr + 0) + 0))) != (int*)(arr)) {
		printf("&(*(*(arr + 0) + 0)) != arr\n");
	} else OK
	
	if (*((int*)arr + 0) != 1){
		printf("*((int*)arr + 0) != 1\n");
	} else OK
	if (*((int*)arr + 1) != 2){
		printf("*((int*)arr + 1) != 2\n");
	} else OK
	if (*((int*)arr + 2) != 3){
		printf("*((int*)arr + 2) != 3\n");
	} else OK
	if (*((int*)arr + 3) != 4){
		printf("*((int*)arr + 3) != 4\n");
	} else OK
	
	// if (
	// Lval(Mem(PlusPI(CastE(TPtr(TInt(int, ), ), StartOf(Var(arr, NoOffset))), Const(Int64(2,int,None))), NoOffset)) 
	// != Const(Int64(3,int,None))) {
	// Lval(Var(printf, NoOffset))(Const(CStr("*((int*)arr + 2) != 3\n")));
	// } else {
	// Lval(Var(printf, NoOffset))(Const(CStr("OK\n")));
	// }
	
	if (*((*(arr + 0)) + 0) != 1){
		printf("*((*(arr + 0)) + 0) != 1\n");
	} else OK
	if (*((*(arr + 0)) + 1) != 2){
		printf("*((*(arr + 0)) + 1) != 2\n");
	} else OK
	if (*((*(arr + 1)) + 0) != 3){
		printf("*((*(arr + 1)) + 0) != 3\n");
	} else OK
	if (*((*(arr + 1)) + 1) != 4){
		printf("*((*(arr + 1)) + 1) != 4\n");
	} else OK
	
	if ((int*)&arr[0] != (int*)&arr[0][0]){
		printf("&arr[0] != &arr[0][0]\n");
	} else OK
	if ((int*)&arr[1] != (int*)&arr[1][0]){
		printf("&arr[1] != &arr[1][0]\n");
	} else OK
	
	struct point pointArr[4];
	pointArr[0].x = 1;
	pointArr[0].y = 2;
	pointArr[1].x = 3;
	pointArr[1].y = 4;
	pointArr[2].x = 5;
	pointArr[2].y = 6;
	pointArr[3].x = 7;
	pointArr[3].y = 8;
	
	if ((*(pointArr + 3)).x != 7) {
		printf("(*(pointArr + 3)).x != 7\n");
	} else OK
	if ((*(pointArr + 3)).y != 8) {
		printf("(*(pointArr + 3)).x != 8\n");
	} else OK
	if (*((int*)(&(*(pointArr + 3)))) != 7) {
		printf("*((int*)(&(*(pointArr + 3)))) != 7\n");
	} else OK
	if (*((int*)(&(*(pointArr + 3))) + 1) != 8) {
		printf("*((int*)(&(*(pointArr + 3))) + 1) != 8\n");
	} else OK
	
	// int x1 = 5;
	// unsigned int x2 = 5;
	// signed int x3 = 5;

	// int y1 = -5;
	// unsigned int y2 = -5;
	// signed int y3 = -5;
	
	// char z1 = 5;
	// unsigned char z2 = 5;
	// signed char z3 = 5;
	
	// int* ugg = (int*)15;
	// printf("ugg+2=%d\n", ugg + 2);
	
	// x1 = z1;
	// x1 = z2;
	// x1 = z3;
	// x2 = z1;
	// x2 = z2;
	// x2 = z3;
	// x3 = z1;
	// x3 = z2;
	// x3 = z3;
	
	// int x = 5;
	// //int dynArr[x];
	// //dynArr[0] = 25;
	// //int q = sizeof(dynArr);
	// int zeroArr[0];
	// // if arr[0][0] == *(arr + 0)
	// // if arr[0][1] == *(arr + 1)
	// // if arr[1][0] == *(arr + 2)
	// // if arr[1][1] == *(arr + 3)
	// printf("zeroArr=%d\n", zeroArr);
	// printf("&zeroArr=%d\n", &zeroArr);
	// printf("arr=%d\n", arr);
	// printf("&arr=%d\n", &arr);
	// printf("&arr[0]=%d\n", &arr[0]);
	// printf("&*(arr + 0)=%d\n", &*(arr + 0));
	// printf("(arr + 0)=%d\n", (arr + 0));
	// printf("&(*(*(arr + 0) + 0))=%d\n", &(*(*(arr + 0) + 0)));
	// printf("&arr[1]=%d\n", &arr[1]);
	// printf("&arr[0][0]=%d\n", &arr[0][0]);
	// printf("&arr[0][1]=%d\n", &arr[0][1]);
	// printf("&arr[1][0]=%d\n", &arr[1][0]);
	// printf("&arr[1][1]=%d\n", &arr[1][1]);
	// printf("arr[0][0]=%d\n", arr[0][0]);
	// printf("arr[0][1]=%d\n", arr[0][1]);
	// printf("arr[1][0]=%d\n", arr[1][0]);
	// printf("arr[1][1]=%d\n", arr[1][1]);
	// printf("sizeof(arr)=%d\n", sizeof(arr)/sizeof(int));
	// printf("sizeof(arr[0])=%d\n", sizeof(arr[0])/sizeof(int));
	// printf("sizeof(int[2][2])=%d\n", sizeof(int[2][2])/sizeof(int));
	//bob(5);
	return 0;
}
// struct bob bob(int x){
	// struct bob z;
	// return z;
// }
