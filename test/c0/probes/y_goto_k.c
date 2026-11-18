#include "c0.h"
//T k u32 : u32 : 0 | 3 | 10
u32 k(u32 n) { u32 r = 0u; u32 i = 0u; while (i < n) { if (i == 5u) goto fin; r += i; i++; } r += 1000u; fin: r += i * 10000u; return r; }
