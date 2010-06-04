   int printf(const char *format, ...);
   struct defs {
     int cbits;          /* No. of bits per char           */
     int ibits;          /*                 int            */
     int sbits;          /*                 short          */
     int lbits;          /*                 long           */
     int ubits;          /*                 unsigned       */
     int fbits;          /*                 float          */
     int dbits;          /*                 double         */
     float fprec;        /* Smallest number that can be    */
     float dprec;        /* significantly added to 1.      */
     int flgs;           /* Print return codes, by section */
     int flgm;           /* Announce machine dependencies  */
     int flgd;           /* give explicit diagnostics      */
     int flgl;           /* Report local return codes.     */
     int rrc;            /* recent return code             */
     int crc;            /* Cumulative return code         */
     char rfs[8];        /* Return from section            */
   };

long pow2(long n) {        /* Calculate 2**n by multiplying, not shifting  */
   long s;
   s = 1;
   while(n--) s = s*2;
   return s;
}


int zerofill(char* x) {
   int j;

   for (j=0; j<256; j++) *x++ = 0;
}
int sumof(char* x) {
   char *p;
   int total, j;

   p = x;
   total = 0;

   for(j=0; j<256; j++) total = total+ *p++;
   return total;
}
