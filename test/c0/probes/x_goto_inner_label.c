#include "c0.h"
//T f u32 : u32 : 0 | 1
u32 f(u32 a) { u32 r = 0u; if (a) goto L; r += 5u; { r += 100u; L: r += 1u; } return r; }
