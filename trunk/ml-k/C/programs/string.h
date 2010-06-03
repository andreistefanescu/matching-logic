// string.h
#define NULL 0
typedef unsigned long int size_t; // this needs to correspond to cfg:sizeut
size_t strlen(char *str);
int strcmp(const char *str1, const char *str2);
char* strcpy(char* s1, const char* s2);
char* strcat(char* dest, const char* src);
char* strchr(const char *s, int c);
void * memset ( void * ptr, int value, size_t num );
void * memcpy ( void * destination, const void * source, size_t num );
