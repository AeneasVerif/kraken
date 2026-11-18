#include "c0.h"
//T c1 bool : u32 : 0 | 1 | 2 | 256 | 0x80000000
bool c1(u32 x) { return (bool)x; }
//T c1b bool : u64 : 0 | 0x100000000 | 1
bool c1b(u64 x) { return (bool)x; }
//T c1c bool : u16 : 0 | 256 | 1
bool c1c(u16 x) { return (bool)x; }
//T c1d u8 : u32 : 0 | 256 | 3
u8 c1d(u32 x) { return (u8)(bool)x; }
//T c1e bool : u32 : 0 | 256 | 3
bool c1e(u32 x) { bool b = x; return b; }
//T c1f bool : u32 : 0 | 256 | 3
bool c1f(u32 x) { return x; }
//T c1g bool : u32 : 0 | 0x100 | 3
bool c1g(u32 x) { return x & 0x100; }
//T c1h u32 : u64 : 0 | 0x100000000 | 3
u32 c1h(u64 x) { bool b = false; b = x; return b; }
//T c1i bool : i64 : 0 | -0x100000000
bool c1i(i64 x) { return (bool)(u8)x == (bool)x; }
//T c2 u64 : u32 : 0 | 1 | 0x7fffffff | 0x80000000 | 0xffffffff
u64 c2(u32 x) { return (u64)(i32)x; }
//T c2b u64 : u32 : 0x80000000 | 0xffffffff
u64 c2b(u32 x) { return (u64)x; }
//T c3 i32 : u32 : 0x80 | 0xff | 0x17f | 0x7f
i32 c3(u32 x) { return (i8)x; }
//T c4 u32 : i64 : -1 | 0x123456789 | -0x100000000
u32 c4(i64 x) { return (u32)x; }
//T c5 u64 : i8 : -1 | -128 | 127
u64 c5(i8 x) { return (u64)x; }
//T c6 u64 : i8 : -1 | -128 | 127
u64 c6(i8 x) { return (u64)(u8)x; }
//T c7 u64 : i16 : -1 | -32768 | 5
u64 c7(i16 x) { return (u32)x; }
//T c8 i64 : u8 : 255 | 128 | 127
i64 c8(u8 x) { return (i8)x; }
//T c9 u32 : bool : 0 | 1
u32 c9(bool b) { return b + b; }
//T c10 u64 : bool : 0 | 1
u64 c10(bool b) { return -b; }
//T c11 u32 : bool bool : 0 1 | 1 0 | 1 1
u32 c11(bool a, bool b) { return a < b; }
//T c12 u64 : i32 : -1 | -16
u64 c12(i32 x) { return (u64)(u32)x >> 4; }
//T c13 u16 : u32 : 0x12345678
u16 c13(u32 x) { return (u16)(x >> 8); }
//T c14 i64 : u64 : 0xffff80000000ffff | 0x7fffffff0000
i64 c14(u64 x) { return (i32)(x >> 16); }
//T c15 bool : i64 : 0 | 0x100000000 | -1
bool c15(i64 x) { return x; }
//T c16 u8 : i32 : -1 | 256 | 0x1ff
u8 c16(i32 x) { return x; }
//T c17 i64 : u32 : 0x80 | 0x7f | 0xff
i64 c17(u32 x) { i8 t = (i8)x; u16 u = t; return u; }
//T c18 i64 : i32 : -1 | 7
i64 c18(i32 x) { return x; }
//T c19 u64 : i32 : -1 | 7
u64 c19(i32 x) { return x; }
//T c20 u64 : i32 : -1 | 7
u64 c20(i32 x) { u64 y = x; return y; }
//T c21 u64 : u32 : 0xffffffff
u64 c21(u32 x) { i64 y = x; return y; }
//T c22 i64 : i32 : -1
i64 c22(i32 x) { u32 y = x; i64 z = y; return z; }
//T c23 i64 : u8 : 200
i64 c23(u8 x) { i8 y = x; return y; }
//T c24 u64 : i64 : -1 | 0x1234
u64 c24(i64 x) { return (u64)(u8 *)x + 1; }
//T c25 u32 : u64 : 0x100000001
u32 c25(u64 x) { u8 *p = (u8 *)x; return (u32)p; }
//T c26 bool : u64 : 0 | 0x100000000
bool c26(u64 x) { u8 *p = (u8 *)x; return p; }
//T c27 i32 : i64 : -1 | 0x7fffffffffffffff
i32 c27(i64 x) { return (i32)(i16)(i8)x + (i32)(u8)(i16)x; }
//T c28 i64 : u64 : 0xffffffffffffffff
i64 c28(u64 x) { return (i64)(i32)(u16)x; }
//T c29 u64 : bool : 1
u64 c29(bool b) { return (u64)b << 40; }
//T c30 i64 : bool : 1 | 0
i64 c30(bool b) { return (i8)b - 2; }
//T f1 f64 : i32 u32 : -1 0xffffffff | 7 2
f64 f1(i32 a, u32 b) { return (f64)a + (f64)b; }
//T f2 i32 : f64 : -1.9 | 1.9 | 0.5 | -0.5
i32 f2(f64 x) { return (i32)x; }
//T f3 f64 : u64 i64 : 0xffffffffffffffff -1 | 1 1
f64 f3(u64 a, i64 b) { return (f64)a * 2.0 + (f64)b; }
//T f4 f64 : i32 : 5
f64 f4(i32 a) { return a / 2 * 1.5 + 1e3 + 0.25 + a; }
//T f5 bool : f64 i32 : 2.5 2 | 2.0 2 | -1.0 0
bool f5(f64 x, i32 y) { return x > y; }
//T f6 u32 : f64 : 3000000000.0 | 7.9
u32 f6(f64 x) { return (u32)x; }
//T f7 bool : f64 : 0.0 | 0.5 | -0.0
bool f7(f64 x) { return (bool)x; }
//T f8 f64 : bool u8 : 1 200
f64 f8(bool b, u8 c) { return (f64)b + c; }
