#include "c0.h"
//T i6b u64 : u64 u32 : 0x500000000 0 | 0x500000000 1
u64 i6b(u64 a, u32 c) { u64 x = a; { u8 x = 3; if (c) { x += 1; } a += x; } return (x >> 32) * 1000u + (u32)a; }
