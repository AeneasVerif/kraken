#include "c0.h"
//T a u32 : f64 f64 : float('nan') 1.0 | 1.0 2.0 | 2.0 2.0 | float('inf') float('nan')
u32 a(f64 x, f64 y) { return (x != x) + (x == x) * 2u + (x < y) * 4u + !(x < y) * 8u + (x >= y) * 16u + (x != y) * 32u + (x > y) * 64u + (x <= y) * 128u; }
//T b f64 : f64 : 0.0 | 1.5 | float('inf')
f64 b(f64 x) { return -x; }
//T c f64 : f64 f64 : 1.0 0.0 | -1.0 0.0 | 7.0 2.0
f64 c(f64 x, f64 y) { return x / y - x * y + 0.1; }
//T d i64 : f64 : -3.99 | 1e15 | 0.99
i64 d(f64 x) { return (i64)x; }
//T e u32 : f64 : 200.7 | 0.3
u32 e(f64 x) { u8 b = (u8)x; u16 w = x; return b + w * 256u; }
//T g bool : f64 : float('nan') | 0.0 | 1.0
bool g(f64 x) { if (x) return true; return false; }
//T h u32 : f64 f64 : float('nan') 1.0 | 1.0 2.0 | 3.0 2.0
u32 h(f64 x, f64 y) { u32 r = 0u; if (x < y && y > 0.5) r += 1u; if (!(x >= y)) r += 2u; r += (x > y ? 4u : 8u); return r; }
//T k f64 : i64 u64 : -1 0xffffffffffffffff | 9007199254740993 9007199254740993
f64 k(i64 a, u64 b) { return (f64)a + (f64)b; }
//T m f64 : u32 i8 : 0xffffffff -1
f64 m(u32 a, i8 b) { f64 r = a; r += b; r = r * 2 + 1; return r / 4; }
