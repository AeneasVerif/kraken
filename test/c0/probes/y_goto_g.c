#include "c0.h"
//T g u32 : u32 u32 : 0 0 | 1 0 | 0 1 | 1 1
u32 g(u32 a, u32 b) { u32 r = 0u; if (a) { r = 5u; if (b) goto done; r += 1u; } else { if (b) { r = 50u; goto done; } } r += 1000u; done: r += 7u; return r; }
