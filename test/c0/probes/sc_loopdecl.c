#include "c0.h"
//T i4 u32 : u32 : 0 | 1 | 4
u32 i4(u32 n) { u32 s = 0u; for (u32 i = 0u; i < n; i++) { u32 t = i * 2u; t += 1u; s += t; } return s; }
//T i5 u32 : u32 : 0 | 1
u32 i5(u32 a) { u32 x = 1u; if (a) { x = 2u; } return x; }
//T i5b u32 : u32 : 0 | 1
u32 i5b(u32 a) { u32 x = 1u; u32 y = 5u; if (a) { } else { x = 2u; y = x + y; } return x * 10u + y; }
//T i5c u32 : u32 : 0 | 1 | 2
u32 i5c(u32 a) { u32 x = 1u; if (a == 0u) { return 50u; } else if (a == 1u) { x = 3u; } return x; }
//T i5d u32 : u32 u32 : 0 0 | 1 0 | 0 1 | 1 1
u32 i5d(u32 a, u32 b) { u32 x = 1u; u32 y = 2u; if (a) { x = 10u; if (b) { y = 20u; } else { x = 30u; } } else { if (b) y = 40u; } return x * 100u + y; }
//T i10 u64 : u32 : 3
u64 i10(u32 a) { u64 s = 0ULL; { u32 t = a; s += t; } { u64 t = 0x100000000ULL; s += t; } { i8 t = -1; s += t; } return s; }
//T i11 u32 : u32 : 0 | 5
u32 i11(u32 n) { u32 s = 0u; u32 i = 0u; while (i < n) { u32 sq = i * i; if (sq > 9u) { u32 d = sq - 9u; s += d; } s += sq; i++; } return s; }
