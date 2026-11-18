#include "c0.h"
//T q1 u32 : u32 u32 u32 : 1 2 3 | 0xf0 0x3c 0xff
u32 q1(u32 a, u32 b, u32 c) { return a | b & c ^ a << 2 + 1 >> 1 == b != c < a; }
//T q2 i32 : i32 i32 : 7 -2 | -7 2
i32 q2(i32 a, i32 b) { return - a * b + a / b - -b % 3 - ~a + !b; }
//T q3 u32 : u32 u32 : 5 3 | 0 0
u32 q3(u32 a, u32 b) { return a & b == b; }
//T q4 i32 : i32 : 5 | -5
i32 q4(i32 a) { return -a - - a + + a - -(-a) + ~~a + !!a + - -a; }
//T q5 u32 : u32 u32 : 5 3
u32 q5(u32 a, u32 b) { return a - b - 1u + a / b / 2u + a % b % 2u + (a << 1 << 1) + (a >> 1 >> 1); }
//T q6 bool : i32 i32 i32 : 1 2 3 | 3 2 1 | 2 2 2
bool q6(i32 a, i32 b, i32 c) { return a < b == b < c; }
//T q7 u64 : p : u8[1,2,3,4,5,6,7,8]
u64 q7(u8 *p) { return *p + *p * *p + (u64)*(u16 *)p + -*p + !*p + sizeof *p + sizeof(*p) * p[1]; }
//T q8 u32 : u32 u32 : 6 3 | 5 0
u32 q8(u32 a, u32 b) { return b != 0u && a / b > 1u ? a / b : b == 0u || a % 2u == 1u ? 77u : 88u; }
//T q9 i64 : i64 : 5 | -5
i64 q9(i64 x) { i64 y = x < 0 ? -x : x; y = y > 3 ? y - 3 : 0; return y; }
//T abs32 i32 : i32 : -5 | 5 | -2147483648
i32 abs32(i32 x) { return x < 0 ? -x : x; }
//T minmax u32 : i32 u32 : -1 5 | 7 5
u32 minmax(i32 a, u32 b) { u32 mn = a < b ? a : b; u32 mx = a > b ? a : b; return mn + mx * 3u; }
