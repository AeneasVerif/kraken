#include "c0.h"
//T i6 u64 : u64 : 0x500000000
u64 i6(u64 a) { u64 x = a; { u8 x = 3; x += 1; a += x; } return (x >> 32) * 1000u + (u32)a; }
