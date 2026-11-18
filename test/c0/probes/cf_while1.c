#include "c0.h"
//T h17b u32 : u32 : 0 | 1 | 17 | 100
u32 h17b(u32 n) { u32 i = 0u; while (1) { if (i * i >= n) return i; i++; } }
