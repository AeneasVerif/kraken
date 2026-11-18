#include "c0.h"
//T h19b u32 : u32 : 0 | 1 | 4 | 5
u32 h19b(u32 n) { u32 x = 0u; for (u32 i = 0u; i < n; i++) { for (u32 j = 0u; j < n; j++) { if (j & 1u) { x = x + 1u; continue; } } } return x; }
