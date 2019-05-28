#ifndef SV_COMP
#define SV_COMP

// This is the API used by the Competition on Software Verification (SV-COMP).
// These functions are usually declared in each problem, so this header
// is not needed for the actual competition, but it is handy when
// trying out other examples.  It also shows the API without having to
// look at the Haskell source.


void __VERIFIER_error(void);
void __VERIFIER_assume(int);
void __VERIFIER_assert(int);
//  __VERIFIER_assert is not part of the API as it can be implemented
// using __VERIFIER_error, but we have an override for nicer errors.


unsigned long   __VERIFIER_nondet_ulong(void);    // 64 bit
long            __VERIFIER_nondet_long(void);     // 64 bit
unsigned int    __VERIFIER_nondet_uint(void);     // 32 bit
int             __VERIFIER_nondet_int(void);      // 32 bit
unsigned short  __VERIFIER_nondet_ushort(void);   // 16 bit
short           __VERIFIER_nondet_short(void);    // 16 bit
unsigned char   __VERIFIER_nondet_uchar(void);    //  8 bit
char            __VERIFIER_nondet_char(void);     //  8 bit
float           __VERIFIER_nondet_float(void);
double          __VERIFIER_nondet_double(void);



#endif
