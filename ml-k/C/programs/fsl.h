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


// stdio.h
int printf(const char *format, ...);
int putchar ( int character );

// string.h
size_t strlen( char *str );
int strcmp( const char *str1, const char *str2 );
char *strcpy(char *restrict s1, const char *restrict s2);
void * memset ( void * ptr, int value, size_t num );

// assert.h
void assert (int expression);
