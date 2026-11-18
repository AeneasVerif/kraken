#include "c0.h"
//T h21 u32 : u32 : 0 | 1 | 2 | 5
u32 h21(u32 n) { u32 s = 0u; for (u32 i = 0u; i < n; i++) { if (i & 1u) { s += 100u; goto next; } s += 1u; next: s += 10u; } return s; }
