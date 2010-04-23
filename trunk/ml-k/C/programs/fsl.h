#define NULL 0
#define EXIT_FAILURE 1
typedef unsigned int size_t;

// stdlib.h
void *malloc(size_t size);
void free(void *pointer);
void *calloc(size_t nelem, size_t elsize);
void exit(int status);

// stdio.h
int printf(const char *format, ...);

// string.h
size_t strlen( char *str );
int strcmp( const char *str1, const char *str2 );
char *strcpy(char *restrict s1, const char *restrict s2);

