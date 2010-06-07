/* This program tests a data flow bug that would cause constant propagation
   to propagate constants through function calls.  */

extern void abort (void);
extern void exit(int status);

foo (int *p)
{
  *p = 10;
}

main()
{
  int *ptr = malloc (sizeof (int));
  *ptr = 5;
  foo (ptr);
  if (*ptr == 5)
    abort ();
  exit (0);
}
