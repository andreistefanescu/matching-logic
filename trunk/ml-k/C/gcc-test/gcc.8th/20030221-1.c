/* PR optimization/8613 */
/* Contributed by Glen Nakamura */
#include <string.h>
extern void abort (void);

int main (void)
{
  char buf[16] = "1234567890";
  char *p = buf;

  *p++ = (char) strlen (buf);

  if ((buf[0] != 10) || (p - buf != 1))
    abort ();

  return 0;
}
