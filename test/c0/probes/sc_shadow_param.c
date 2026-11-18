#include "c0.h"
//T i9 u32 : u32 : 0 | 3
u32 i9(u32 a) { u32 s = 0u; for (u32 i = 0u; i < 3u; i++) { u32 a = i * 10u; s += a; } return s + a * 1000u; }
