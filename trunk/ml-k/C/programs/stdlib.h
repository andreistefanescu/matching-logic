// stdlib.h
#define EXIT_FAILURE 1
# define RAND_MAX 2147483647
void *malloc(size_t size);
void free(void *pointer);
void *calloc(size_t nelem, size_t elsize);
void exit(int status);
void debug(int i);
void srand (unsigned int seed);
int rand (void);
