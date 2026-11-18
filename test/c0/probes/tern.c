#include "c0.h"
//T t1 i64 : bool u8 : 1 200 | 0 200
i64 t1(bool c, u8 x) { return c ? x : -1; }
//T t2 i64 : bool i32 u32 : 1 -1 5 | 0 -1 5
i64 t2(bool c, i32 a, u32 b) { return c ? a : b; }
//T t3 i64 : bool u32 i64 : 1 7 -5 | 0 7 -5 | 0 7 0x123456789
i64 t3(bool c, u32 a, i64 b) { return c ? a : b; }
//T t4 u64 : bool i32 u64 : 1 -1 5 | 0 -1 0x123456789
u64 t4(bool c, i32 a, u64 b) { return c ? a : b; }
//T t5 u32 : bool u32 : 1 7 | 0 7 | 0 0
u32 t5(bool c, u32 x) { return c ? (x > 3u) : x; }
//T t6 bool : bool p : 0 u32[1] | 1 u32[1]
bool t6(bool c, u32 *p) { return (c ? 0 : p) == p; }
//T t7 i64 : bool i8 i64 : 1 -1 5 | 0 -1 300
i64 t7(bool c, i8 a, i64 b) { i64 r = c ? a : b; return r; }
//T t8 i64 : bool u32 : 1 5 | 0 5
i64 t8(bool c, u32 a) { return c ? 1 : a - 6u; }
//T t9 i64 : bool i32 : 1 -5 | 0 -5
i64 t9(bool c, i32 a) { return (c ? 1u : a) / 2; }
//T t10 bool : bool i32 : 0 -5 | 1 -5
bool t10(bool c, i32 a) { return (c ? a : 0u) < 1; }
//T t11 i64 : bool : 0 | 1
i64 t11(bool c) { return c ? 1 : 5000000000LL; }
//T t12 u64 : bool i32 : 0 -1 | 1 -1
u64 t12(bool c, i32 a) { return sizeof(c ? a : 1LL); }
//T t13 f64 : bool i32 : 0 3 | 1 3
f64 t13(bool c, i32 a) { return c ? a : 0.5; }
