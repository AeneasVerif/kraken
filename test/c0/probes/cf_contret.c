#include "c0.h"
//T h18b u32 : u32 : 0 | 1 | 2 | 5
u32 h18b(u32 n) { u32 x = 0u; u32 i = 0u; for (;;) { x += 2u; i++; if (i < n) continue; return x; } }
