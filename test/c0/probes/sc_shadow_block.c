#include "c0.h"
//T i1 u32 : u32 : 0 | 3
u32 i1(u32 a) { u32 x = a; { u32 x = 7u; x = x + 1u; a = a + x; } return x * 1000u + a; }
