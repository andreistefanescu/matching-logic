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

long pow2(int n){
	long retval = 1;
	for (int i = 0; i < n; i++){
		retval *= (long)2;
	}
	return retval;
}
