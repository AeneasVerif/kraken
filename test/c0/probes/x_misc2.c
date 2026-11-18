#include "c0.h"
//T a u32 : u32 : 5
u32 a(u32 x) { u32 y = -1; u8 z = 300; i8 w = 200; u16 v = -x; return y + z + w + v; }
//T b u64 : :
u64 b(void) { u64 x = (u64)NULL; u8 *p = NULL; return x + (u64)p + (p == NULL) + sizeof(NULL); }
//T c u32 : u32 u32 u32 : 1 2 3 | 0 0 0
static inline u32 pick(bool c, u32 a, u32 b) { return c ? a : b; }
u32 c(u32 x, u32 y, u32 z) { return pick(x && y, z ? x : y, pick(!z, 5u, 6u)); }
//T d u32 : u32 u32 u32 : 1 9 3 | 0 9 3
u32 d(u32 c, u32 n, u32 m) { u32 i = 0u; while (i < (c ? n : m)) { i++; } return i; }
//T e u32 : u32 : 5 | 0
static u32 helper(u32 x) { return x ? x * 2u : 9u; }
inline u32 helper2(u32 x) { return helper(x) + 1u; }
u32 e(u32 x) { return helper2(x) + helper(x + 1u); }
//T f i32 : i32 i32 : 2147483647 1 | -2147483648 -1 | 65536 65536
i32 f(i32 a, i32 b) { return (a + b) ^ (a - b) ^ (a * b); }
//T g u32 : u32 : 0 | 5
u32 g(u32 x) { u32 r = 0u; if (x) ; else r = 3u; ; ; { } return r + x; }
//T h u64 : u64 : 5
u64 h(u64 x) { const u64 k = 3ULL; volatile u64 y = x; u64 const z = y + k; return z; }
