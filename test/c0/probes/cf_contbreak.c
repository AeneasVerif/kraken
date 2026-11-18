#include "c0.h"
//T h18 u32 : u32 : 0 | 1 | 2 | 5
u32 h18(u32 n) { u32 x = 0u; u32 i = 0u; while (true) { x += 2u; i++; if (i < n) continue; break; } return x; }
