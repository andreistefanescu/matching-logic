#include "fsl.h"
// struct bob {
	// int x;
// };
// struct bob bob(int);

int main(void){
	int arr[2][2] = {{1, 2}, {3, 4}};
	
	int x1 = 5;
	unsigned int x2 = 5;
	signed int x3 = 5;

	int y1 = -5;
	unsigned int y2 = -5;
	signed int y3 = -5;
	
	char z1 = 5;
	unsigned char z2 = 5;
	signed char z3 = 5;
	
	int* ugg = (int*)15;
	printf("ugg+2=%d\n", ugg + 2);
	
	x1 = z1;
	x1 = z2;
	x1 = z3;
	x2 = z1;
	x2 = z2;
	x2 = z3;
	x3 = z1;
	x3 = z2;
	x3 = z3;
	
	int x = 5;
	//int dynArr[x];
	//dynArr[0] = 25;
	//int q = sizeof(dynArr);
	int zeroArr[0];
	// if arr[0][0] == *(arr + 0)
	// if arr[0][1] == *(arr + 1)
	// if arr[1][0] == *(arr + 2)
	// if arr[1][1] == *(arr + 3)
	printf("zeroArr=%d\n", zeroArr);
	printf("&zeroArr=%d\n", &zeroArr);
	printf("arr=%d\n", arr);
	printf("&arr=%d\n", &arr);
	printf("&arr[0]=%d\n", &arr[0]);
	printf("&*(arr + 0)=%d\n", &*(arr + 0));
	printf("(arr + 0)=%d\n", (arr + 0));
	printf("&(*(*(arr + 0) + 0))=%d\n", &(*(*(arr + 0) + 0)));
	printf("&arr[1]=%d\n", &arr[1]);
	printf("&arr[0][0]=%d\n", &arr[0][0]);
	printf("&arr[0][1]=%d\n", &arr[0][1]);
	printf("&arr[1][0]=%d\n", &arr[1][0]);
	printf("&arr[1][1]=%d\n", &arr[1][1]);
	printf("arr[0][0]=%d\n", arr[0][0]);
	printf("arr[0][1]=%d\n", arr[0][1]);
	printf("arr[1][0]=%d\n", arr[1][0]);
	printf("arr[1][1]=%d\n", arr[1][1]);
	printf("sizeof(arr)=%d\n", sizeof(arr)/sizeof(int));
	printf("sizeof(arr[0])=%d\n", sizeof(arr[0])/sizeof(int));
	printf("sizeof(int[2][2])=%d\n", sizeof(int[2][2])/sizeof(int));
	//bob(5);
	return 0;
}
// struct bob bob(int x){
	// struct bob z;
	// return z;
// }