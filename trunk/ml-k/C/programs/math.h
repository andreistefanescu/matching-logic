// math.h (real c99 needs -lm to get math library linked in)
double sqrt (double x);
double cos(double x);
int abs( int num );
int abs( int num ){
	if (num >= 0) {
		return num;
	} else {
		return -num;
	}
}
