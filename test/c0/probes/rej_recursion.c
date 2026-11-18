#include "c0.h"
//T f u32 : u32 : 5
u32 f(u32 n) { if (n == 0u) return 1u; return n * f(n - 1u); }
