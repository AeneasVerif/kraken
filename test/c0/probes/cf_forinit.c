#include "c0.h"
//T h20 u32 : u32 : 0 | 2 | 3 | 10
u32 h20(u32 n) { u32 j = 100u; u32 s = 0u; for (j = 0u; s < n; s++) { if (s == 3u) break; } return j * 1000u + s; }
