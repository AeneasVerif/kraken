#include "c0.h"
//T i2 u32 : u32 : 0 | 9
u32 i2(u32 a) { u32 x = a; if (a > 5u) { u32 x = 1u; a = x + 100u; } return x * 1000u + a; }
