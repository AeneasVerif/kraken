#include "c0.h"
//T i7 u32 : u32 : 0 | 1
u32 i7(u32 v) { u32 x = 5u; u32 r = 0u; switch (v) { case 0: { u32 x = 9u; r = x; break; } default: r = 1u; break; } return x * 100u + r; }
