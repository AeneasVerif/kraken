#include "c0.h"
//T h8c u32 : u32 : 0 | 1 | 2 | 3
u32 h8c(u32 v) { u32 r = 0u; switch (v) { default: r += 50u; break; case 1: r += 1u; fallthrough; case 2: r += 7u; } return r; }
