#define NULL 0
typedef unsigned long int size_t;
// nice pd implementations at http://en.wikibooks.org/wiki/C_Programming/Strings
char *strcpy(char *dest, const char *src)
{
  unsigned i;
  for (i=0; src[i] != '\0'; ++i)
    dest[i] = src[i];
  dest[i] = '\0';
  return dest;
}

size_t strlen(const char * str)
{
    const char *s;
    for (s = str; *s; ++s);
    return(s - str);
}

void* memset (void* dest, int value, size_t len) {
	unsigned char *ptr = (unsigned char*)dest;
	while (len-- > 0) {
		*ptr++ = value;
	}
	return dest;
}

int strcmp (const char * s1, const char * s2) {
    for(; *s1 == *s2; ++s1, ++s2)
        if(*s1 == 0)
            return 0;
    return *(unsigned char *)s1 < *(unsigned char *)s2 ? -1 : 1;
}

char *(strchr)(const char *s, int c) {
 /* Scan s for the character.  When this loop is finished,
	s will either point to the end of the string or the
	character we were looking for.  */
 while (*s != '\0' && *s != (char)c)
	 s++;
 return ( (*s == c) ? (char *) s : NULL );
}


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

char * strcat(char *dest, const char *src){
    strcpy(dest + strlen(dest), src);
    return dest;
}


int puts(const char * str){
	return printf("%s\n", str);
}