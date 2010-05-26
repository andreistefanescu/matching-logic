// string.h
size_t strlen(char *str);
int strcmp(const char *str1, const char *str2);
char* strcpy(char *restrict s1, const char *restrict s2);
char* strcat(char* dest, const char* src);
char * strcat(char *dest, const char *src){
    strcpy(dest + strlen(dest), src);
    return dest;
}

char* strchr(const char *s, int c);
char* strchr(const char *s, int c){
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
