#include "c0.h"
//T f u32 : u32 : 0 | 1 | 5
u32 f(u32 n) { u32 i = 0u; u32 s = 0u; do { i++; switch (i & 1u) { case 1: continue; default: break; } s += i; } while (i < n); return s * 100u + i; }
