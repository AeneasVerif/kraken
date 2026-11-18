#include "c0.h"
//T h u32 : u32 : 0 | 1 | 2 | 3
u32 h(u32 a) { u32 r = 0u; switch (a) { case 0: r = 1u; goto out; case 1: r = 2u; break; default: if (a == 2u) goto out; r = 3u; break; } r += 100u; out: return r; }
