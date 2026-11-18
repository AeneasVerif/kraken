#include "c0.h"
typedef struct { u16 x; i8 y; bool z; u32 w; } s8;
//T g u64 : u32 : 0 | 3
u64 g(u32 n) { s8 v = {0}; u32 i = 0u; while (i < n) { v.x = v.x + 3; v.y = v.y - 1; v.z = !v.z; v.w = v.w * 2u + 1u; i++; } i32 y = v.y; return v.x + (u64)(u32)y * 3u + v.z * 5u + (u64)v.w * 7u; }
//T h u64 : u32 : 0 | 3
u64 h(u32 n) { s8 a = {0}; a.x = n; a.w = n * 5u; s8 b = a; b.x = 9; if (n) { a = b; a.y = -1; } i32 y = a.y; return a.x + (u64)(u32)y * 3u + (u64)a.w * 7u + b.x * 1000u; }
