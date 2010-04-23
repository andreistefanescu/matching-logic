int a = 5;
int* b = &a;
int c = a;

int main(void){
	return a + *b + c;
}