#include "c0.h"
//T f u32 : u32 u32 : 1 0 | 2 1 | 3 0 | 4 1 | 9 9
u32 f(u32 v, u32 a) { u32 r = 0u; switch (v) { case 1: case 2: if (a) r = 1u; else r = 2u; r += 5u; break; case 3: case 4: case 5: for (u32 i = 0u; i < v; i++) { r += i; if (a && i == 2u) break; } break; default: r = 77u; break; } return r; }
//T g u32 : u32 u32 : 1 0 | 2 1 | 3 0 | 4 1 | 9 9
u32 g(u32 v, u32 a) { u32 r = 0u; switch (v) { case 1: r += 1u; fallthrough; case 2: if (a) { r += 10u; } fallthrough; case 3: case 4: r += (a && v > 3u) ? 100u : 200u; break; } return r; }
