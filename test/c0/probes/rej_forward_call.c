#include "c0.h"
u32 later(u32 x);
//T k4 u32 : u32 : 1 | 7
u32 k4(u32 x) { return later(x) + 1u; }
u32 later(u32 x) { return x * 3u; }
