#include "c0.h"
//T i3b u32 : u32 : 0 | 4 | 9
u32 i3b(u32 n) { u32 i = 77u; u32 s = 0u; for (u32 i = 0u; i < n; i++) { if (i == 5u) break; s += i; } return i * 1000u + s; }
