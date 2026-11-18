#include "c0.h"
//T h19 u32 : p u32 u32 : u32[2,0,1,0] 3 4 | u32[9,9] 3 2 | u32[] 0 0
u32 h19(u32 *a, u32 n, u32 m) { u32 found = 0u; for (u32 i = 0u; i < n; i++) { for (u32 j = 0u; j < m; j++) { if (a[j] == i) { found += j + 1u; break; } } } return found; }
