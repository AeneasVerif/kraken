#include "c0.h"
//T d1 i32 : i32 i32 : -7 2 | 7 -2 | -7 -2 | 7 2 | -2147483648 1 | -2147483647 -1 | 0 -5 | -1 2
i32 d1(i32 a, i32 b) { return a / b; }
//T d2 i32 : i32 i32 : -7 2 | 7 -2 | -7 -2 | 7 2 | -2147483648 1 | -2147483647 -1 | 0 -5 | -1 2 | -8 4
i32 d2(i32 a, i32 b) { return a % b; }
//T d3 i64 : i64 i64 : -7 2 | 7 -2 | -7 -2 | -0x8000000000000000 3 | 0x7fffffffffffffff -1
i64 d3(i64 a, i64 b) { return a / b; }
//T d4 i64 : i64 i64 : -7 2 | 7 -2 | -7 -2 | -0x8000000000000000 3 | 0x7fffffffffffffff -1
i64 d4(i64 a, i64 b) { return a % b; }
//T d5 i32 : i8 i8 : -128 -1 | -7 2 | 127 -128
i32 d5(i8 a, i8 b) { return a / b; }
//T d5m i32 : i8 i8 : -128 -1 | -7 2 | 127 -128
i32 d5m(i8 a, i8 b) { return a % b; }
//T d6 u32 : i32 u32 : -7 2 | 7 2
u32 d6(i32 a, u32 b) { return a / b; }
//T d6m u32 : i32 u32 : -7 2 | 7 2
u32 d6m(i32 a, u32 b) { return a % b; }
//T d7 i64 : i64 u32 : -7 2 | -1 0xffffffff
i64 d7(i64 a, u32 b) { return a % b; }
//T d8 u8 : u8 u8 : 255 2 | 200 7
u8 d8(u8 a, u8 b) { return a / b; }
//T d9 i32 : i16 u16 : -7 2 | -32768 65535
i32 d9(i16 a, u16 b) { return a % b; }
//T d10 u64 : u64 u64 : 0xffffffffffffffff 2 | 0x8000000000000000 0xffffffff
u64 d10(u64 a, u64 b) { return a / b + a % b; }
//T d11 i32 : i32 : -7 | 7 | -8 | -1
i32 d11(i32 a) { return a / 2 + a % 2 * 10 + a / -3 * 100; }
//T d12 u32 : u32 : 0xffffffff | 7
u32 d12(u32 a) { return a / 2 + a % 3; }
//T d13 i64 : i32 i64 : -7 2
i64 d13(i32 a, i64 b) { return a / b * 10 + a % b; }
//T d14 u32 : u16 i8 : 65535 -1 | 7 -2
u32 d14(u16 a, i8 b) { return a / b; }
//T d15 i32 : i32 i32 : -2147483648 -1
i32 d15(i32 a, i32 b) { return a * b + (a - 1) + (-a); }
