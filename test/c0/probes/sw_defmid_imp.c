#include "c0.h"
//T h5 u32 : u32 : 0 | 1 | 2
u32 h5(u32 v) { u32 r = 0u; switch (v) { case 0: r += 1u; break; default: r += 9u; case 1: r += 2u; break; } return r; }
