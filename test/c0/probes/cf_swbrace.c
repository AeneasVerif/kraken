#include "c0.h"
//T h12 u32 : p u32 : u32[1,2,1,3,2] 5 | u32[] 0 | u32[1] 1
u32 h12(u32 *a, u32 n) { u32 x = 0u; u32 y = 0u; for (u32 i = 0u; i < n; i++) { switch (a[i]) { case 1: { x += 1u; break; } case 2: if (x > 0u) { y += 10u; break; } y += 1u; break; default: break; } } return x * 100u + y; }
