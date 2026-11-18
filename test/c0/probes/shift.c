#include "c0.h"
//T s1 i32 : i32 u32 : -8 1 | -1 31 | 0x7fffffff 3 | -2147483648 31
i32 s1(i32 x, u32 n) { return x >> n; }
//T s2 i64 : i64 u8 : -8 1 | -1 63 | 0x7fffffffffffffff 62 | -0x8000000000000000 40
i64 s2(i64 x, u8 n) { return x >> n; }
//T s3 u32 : u32 i64 : 0x80000000 31 | 0xffffffff 4 | 1 0
u32 s3(u32 x, i64 n) { return x >> n; }
//T s4 u64 : u8 u64 : 0x80 24 | 1 31 | 0xff 8 | 0x7f 24
u64 s4(u8 x, u64 n) { return x << n; }
//T s5 u64 : u64 u8 : 1 40 | 1 63 | 0xffffffff 32
u64 s5(u64 x, u8 n) { return x << n; }
//T s6 i32 : i8 i8 : -128 3 | -1 7 | 127 1
i32 s6(i8 x, i8 n) { return x >> n; }
//T s7 u64 : u16 : 0xffff | 1 | 0x8000
u64 s7(u16 x) { return x << 16; }
//T s8 i64 : i32 : 0x10000000 | -1 | 0x7fffffff
i64 s8(i32 x) { return x << 3; }
//T s9 u32 : u32 u32 : 0x80000001 1 | 0x12345678 31 | 0xdeadbeef 16
u32 s9(u32 x, u32 n) { return (x << n) | (x >> (32u - n)); }
//T s10 i16 : i16 u32 : -32768 15 | -2 1 | 0x7fff 14
i16 s10(i16 x, u32 n) { return x >> n; }
//T s11 u64 : i32 u64 : -16 2 | 16 2
u64 s11(i32 x, u64 n) { return x >> n; }
//T s12 u8 : u8 : 0x81 | 0x01 | 0xfe
u8 s12(u8 x) { return (x >> 1) | (x << 7); }
//T s13 u64 : u32 : 0xffffffff | 1
u64 s13(u32 x) { return x << 4; }
//T s14 u64 : u32 : 0xffffffff | 1
u64 s14(u32 x) { return (u64)x << 4; }
//T s15 u64 : u8 : 0xff
u64 s15(u8 x) { return (u64)x << 56 | x >> 1; }
//T s16 i64 : i64 i32 : -256 4 | 256 4
i64 s16(i64 x, i32 n) { return (x >> n) + (x << n); }
//T s17 u32 : u16 u8 : 0xffff 15 | 0x8000 15
u32 s17(u16 x, u8 n) { return x >> n << n; }
//T s18 u64 : i8 : -1 | -128
u64 s18(i8 x) { return (u8)x >> 1; }
//T s19 i32 : u8 : 0xff | 0x80
i32 s19(u8 x) { return (i8)x >> 1; }
//T s20 u64 : u64 u64 : 0x8000000000000000 63 | 0xf0 4
u64 s20(u64 x, u64 n) { u64 r = x; r >>= n; r <<= 1; return r; }
//T s21 i32 : i32 i64 : -64 3
i32 s21(i32 x, i64 n) { x >>= n; return x; }
