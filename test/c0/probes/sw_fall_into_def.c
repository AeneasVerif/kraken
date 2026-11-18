#include "c0.h"
//T h7 u32 : u32 : 0 | 1 | 2
u32 h7(u32 v) { u32 r = 0u; switch (v) { case 0: r += 1u; fallthrough; default: r += 9u; break; case 1: r += 2u; break; } return r; }
