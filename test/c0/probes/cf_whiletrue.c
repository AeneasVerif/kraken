#include "c0.h"
//T h17c u32 : u32 : 0 | 1 | 17 | 100
u32 h17c(u32 n) { u32 i = 0u; while (true) { if (i * i >= n) return i; i++; } }
