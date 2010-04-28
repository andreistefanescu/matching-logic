#define NULL 0
#define EXIT_FAILURE 1
typedef unsigned int size_t;

// stdlib.h
# define RAND_MAX 2147483647
void *malloc(size_t size);
void free(void *pointer);
void *calloc(size_t nelem, size_t elsize);
void exit(int status);
void debug(int i);
int atoi ( const char * str );
void srand (unsigned int seed);
int rand (void);

// math.h
double sqrt (double x);

// stdio.h
int printf(const char *format, ...);
//extern int printf (__const char *__restrict __format, ...);
int putchar ( int character );
int sprintf ( char * str, const char * format, ... );
#define EOF -1
//size_t fwrite ( const void * ptr, size_t size, size_t count, FILE * stream );
//#define FILE int
//int fwrite( const void *buffer, size_t size, size_t count, FILE *stream );

int puts (const char * str);
int puts(const char * str){
	return printf("%s\n", str);
}
//#define stdout 1 

// string.h
size_t strlen( char *str );
int strcmp( const char *str1, const char *str2 );
char *strcpy(char *restrict s1, const char *restrict s2);
char* 	strchr (const char *s, int c);
char* 	strchr (const char *s, int c){
	int i = 0;
	if (s == NULL){
		return NULL;
	}
	while (1){
		if (s[i] == c){
			return (char*)(&(s[i]));
		} else if (s[i] == 0){
			return NULL;
		}
		i++;
	}
}
void * memset ( void * ptr, int value, size_t num );
void * memcpy ( void * destination, const void * source, size_t num );
// from http://www.danielvik.com/2010/02/fast-memcpy-in-c.html
// by Daniel Vik
void* memcpy(void* dest, const void* src, size_t count) {
	char* dst8 = (char*)dest;
	char* src8 = (char*)src;

	while (count--) {
		*dst8++ = *src8++;
	}
	return dest;
}

// assert.h
void assert (int expression);

// time.h
typedef unsigned int time_t;
time_t time ( time_t * timer );


