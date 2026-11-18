#include "c0.h"
//T h8 u32 : u32 : 0 | 1 | 2 | 3
u32 h8(u32 v) { u32 r = 0u; switch (v) { case 1: default: r += 5u; break; case 2: r += 7u; break; } return r; }
