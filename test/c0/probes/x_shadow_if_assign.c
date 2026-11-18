#include "c0.h"
//T f u32 : u32 : 0 | 9
u32 f(u32 a) { u32 x = a; if (a > 5u) { u32 x = 1u; x += 100u; a = x; } return x * 1000u + a; }
