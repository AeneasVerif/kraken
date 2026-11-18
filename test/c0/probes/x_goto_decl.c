#include "c0.h"
//T f u32 : u32 : 0 | 1
u32 f(u32 a) { u32 r = 0u; if (a) goto L; u32 t = 5u; r += t; L: r += 1u; return r; }
