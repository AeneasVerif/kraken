#include "c0.h"
//T h26 u32 : u32 : 0 | 1 | 5
u32 h26(u32 a) { u32 r = 0u; if (a < 3u) { if (a == 0u) { r = 5u; goto L; } else { r = 6u; goto L; } L: r += 1u; } r += 10u; return r; }
