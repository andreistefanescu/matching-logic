#include <stdio.h>

struct bfs {
	unsigned int a0 : 1;
	unsigned int a1 : 1;
	unsigned int a2 : 1;
	unsigned int a3 : 1;
	unsigned int a4 : 1;
	unsigned int a5 : 1;
	unsigned int a6 : 1;
	unsigned int a7 : 1; // boundary
	unsigned int b0 : 2;
	unsigned int b1 : 2;
	unsigned int b2 : 2;
	unsigned int b3 : 2; // boundary
	unsigned int c1 : 4;
	unsigned int c2 : 4; // boundary
	unsigned int d : 8; // boundary
	unsigned int e : 16; // boundary
	unsigned int f : 7;
	unsigned int g;
	unsigned int h;
	unsigned int i : 4;
	unsigned int : 0;
	unsigned int j;
};
struct bfs s;

int testOnes(void){
	struct bfs* p = &s;
	s.a0 = 0;
	s.a1 = 0;
	s.a2 = 0;
	s.a3 = 0;
	s.a4 = 0;
	s.a5 = 0;
	s.a6 = 0;
	s.a7 = 0;
	if (s.a0 != 0){ puts("BUG: a0"); }
	if (s.a1 != 0){ puts("BUG: a0"); }
	if (s.a2 != 0){ puts("BUG: a0"); }
	if (s.a3 != 0){ puts("BUG: a0"); }
	if (s.a4 != 0){ puts("BUG: a0"); }
	if (s.a5 != 0){ puts("BUG: a0"); }
	if (s.a6 != 0){ puts("BUG: a0"); }
	if (s.a7 != 0){ puts("BUG: a0"); }
	s.a0 = 1;
	s.a1 = 1;
	s.a2 = 1;
	s.a3 = 1;
	s.a4 = 1;
	s.a5 = 1;
	s.a6 = 1;
	s.a7 = 1;
	if (s.a0 != 1){ puts("BUG: a1"); }
	if (s.a1 != 1){ puts("BUG: a1"); }
	if (s.a2 != 1){ puts("BUG: a1"); }
	if (s.a3 != 1){ puts("BUG: a1"); }
	if (s.a4 != 1){ puts("BUG: a1"); }
	if (s.a5 != 1){ puts("BUG: a1"); }
	if (s.a6 != 1){ puts("BUG: a1"); }
	if (s.a7 != 1){ puts("BUG: a1"); }
	s.a0 = 1;
	s.a1 = 0;
	s.a2 = 1;
	s.a3 = 1;
	s.a4 = 0;
	s.a5 = 1;
	s.a6 = 1;
	s.a7 = 1;
	if (s.a0 != 1){ puts("BUG: a2"); }
	if (s.a1 != 0){ puts("BUG: a2"); }
	if (s.a2 != 1){ puts("BUG: a2"); }
	if (s.a3 != 1){ puts("BUG: a2"); }
	if (s.a4 != 0){ puts("BUG: a2"); }
	if (s.a5 != 1){ puts("BUG: a2"); }
	if (s.a6 != 1){ puts("BUG: a2"); }
	if (s.a7 != 1){ puts("BUG: a2"); }
	s.a6 = 0;
	if (s.a5 != 1){ puts("BUG: a3"); }
	if (s.a6 != 0){ puts("BUG: a3"); }
	if (s.a7 != 1){ puts("BUG: a3"); }
	unsigned char firstChar = (char)*((char*)&s);
	if (firstChar == 181){
		puts("VOLATILE: top bits are MSB");
		puts("byte interp OK");
	} else if (firstChar == 173) {
		puts("VOLATILE: top bits are LSB");
		puts("byte interp OK");
	} else {
		puts("BUG: a4");
	}
	p->a6 = 1;
	if (p->a5 != 1){ puts("BUG: a4"); }
	if (p->a6 != 1){ puts("BUG: a4"); }
	if (p->a7 != 1){ puts("BUG: a4"); }
	return 0;
}

int testTwos(){
	struct bfs* p = &s;
	s.b0 = 0;
	s.b1 = 0;
	s.b2 = 0;
	s.b3 = 0;
	if (s.b0 != 0){ puts("BUG: b0"); }
	if (s.b1 != 0){ puts("BUG: b0"); }
	if (s.b2 != 0){ puts("BUG: b0"); }
	if (s.b3 != 0){ puts("BUG: b0"); }
	s.b0 = 1;
	s.b1 = 1;
	s.b2 = 1;
	s.b3 = 1;
	if (s.b0 != 1){ puts("BUG: b1"); }
	if (s.b1 != 1){ puts("BUG: b1"); }
	if (s.b2 != 1){ puts("BUG: b1"); }
	if (s.b3 != 1){ puts("BUG: b1"); }
	s.b0 = 2;
	s.b1 = 2;
	s.b2 = 2;
	s.b3 = 2;
	if (s.b0 != 2){ puts("BUG: b2"); }
	if (s.b1 != 2){ puts("BUG: b2"); }
	if (s.b2 != 2){ puts("BUG: b2"); }
	if (s.b3 != 2){ puts("BUG: b2"); }
	s.b0 = 1;
	s.b1 = 0;
	s.b2 = 2;
	s.b3 = 3;
	if (s.b0 != 1){ puts("BUG: b3"); }
	if (s.b1 != 0){ puts("BUG: b3"); }
	if (s.b2 != 2){ puts("BUG: b3"); }
	if (s.b3 != 3){ puts("BUG: b3"); }
	s.b0 = 3;
	s.b1 = 2;
	s.b2 = 0;
	s.b3 = 1;
	if (s.b0 != 3){ puts("BUG: b4"); }
	if (s.b1 != 2){ puts("BUG: b4"); }
	if (s.b2 != 0){ puts("BUG: b4"); }
	if (s.b3 != 1){ puts("BUG: b4"); }
	// 11 10 00 01 => 10000111
	// 01 00 10 11 => 01001011
	unsigned char firstChar = (char)*(((char*)&(s))+1);
	if (firstChar == 135){
		puts("VOLATILE: top bits are MSB");
		puts("byte interp OK");
	} else if (firstChar == 75) {
		puts("VOLATILE: top bits are LSB");
		puts("byte interp OK");
	} else {
		printf("BUG: b5: %d\n", firstChar);
	}
}

int main(void){
	testOnes();
	testTwos();
	return 0;
}
