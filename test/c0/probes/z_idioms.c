#include "c0.h"
//T f u32 : u32 : 0 | 3 | 20
u32 f(u32 n) { u32 r = 0u; u32 i = 0u; while (true) { if (i >= n) break; r += i; i++; } return r; }
//T g u32 : u32 : 0 | 3 | 20
u32 g(u32 n) { u32 r = 0u; for (u32 i = 0u; ; i++) { if (i >= n) break; if (i == 10u) { r = 777u; break; } r += i; } return r; }
//T h u32 : u32 : 0 | 3 | 20
u32 h(u32 n) { u32 r = 0u; u32 i = 0u; do { if (i >= n) break; r += i; i++; } while (true); return r; }
//T k u32 : u32 : 0 | 3 | 20
u32 k(u32 n) { u32 r = 0u; u32 i = n; while (i) { i--; if (i % 3u == 0u) continue; r += i; } return r; }
