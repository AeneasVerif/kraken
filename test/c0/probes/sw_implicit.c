#include "c0.h"
//T h6 u32 : u32 : 0 | 1 | 2
u32 h6(u32 v) { u32 r = 0u; switch (v) { case 0: r += 1u; case 1: r += 2u; break; default: r += 100u; break; } return r; }
