#include "c0.h"
typedef union { struct { u32 lit:31; u32 binary:1; } b; u32 raw; } watch;
typedef struct { u16 x; i8 y; bool z; u32 w; } s8;
//T f u32 : u32 : 0 | 3 | 40
u32 f(u32 n) { watch w = {0}; for (u32 i = 0u; i < n; i++) { w.b.lit = w.b.lit + i; if (i == 2u) { w.b.binary = true; } } return w.raw; }
//T g u64 : u32 : 0 | 3
u64 g(u32 n) { s8 v = {0}; u32 i = 0u; while (i < n) { v.x += 3; v.y -= 1; v.z = !v.z; v.w = v.w * 2u + 1u; i++; } i32 y = v.y; return v.x + (u64)(u32)y * 3u + v.z * 5u + (u64)v.w * 7u; }
