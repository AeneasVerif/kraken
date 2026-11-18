#include "c0.h"
//T i12 u32 : u32 : 0 | 3
u32 i12(u32 n) { u32 t = 500u; u32 s = 0u; u32 i = 0u; while (i < n) { u32 t = i; t += 1u; s += t; i++; } return s + t; }
