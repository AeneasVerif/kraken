#include "c0.h"
//T f u32 : : 
u32 f(void) { u32 c = 0u; for (u8 i = 250; i != 4; i++) { c++; } return c; }
//T g i32 : : 
i32 g(void) { i32 c = 0; i8 i = 120; while (i > 0) { i += 3; c++; } return c * 1000 + i; }
//T h u32 : u32 : 0 | 5
u32 h(u32 n) { bool t = false; u32 c = 0u; for (u32 i = 0u; i < n; i++) { t = !t; if (t) c++; } return c * 10u + t; }
//T k u32 : u32 : 5 | 300
u32 k(u32 n) { u8 x = 0; u16 y = 0; i8 z = 0; for (u32 i = 0u; i < n; i++) { x++; y += 250; z--; } i32 zz = z; return x + y * 256u + (u32)zz; }
