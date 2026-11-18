#include "c0.h"
//T f u32 : u32 u32 : 0 0 | 1 0 | 0 1 | 1 1
u32 f(u32 a, u32 b) { u32 r = 0u; if (a) goto L1; r += 1u; if (b) goto L2; r += 2u; L1: r += 10u; L2: r += 100u; return r; }
