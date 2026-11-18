#include "c0.h"
#define N 4
//T f u32 : :
u32 f(void) { return N; }
#undef N
#define N 8
//T g u32 : :
u32 g(void) { return N; }
