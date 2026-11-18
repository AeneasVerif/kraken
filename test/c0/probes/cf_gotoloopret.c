#include "c0.h"
//T h27 u32 : p u32 : u32[0,0,7,0] 4 | u32[0,0] 2 | u32[] 0
u32 h27(u32 *p, u32 n) { u32 i = 0u; while (i < n) { if (p[i] == 0u) goto next; return i; next: i++; } return 99u; }
