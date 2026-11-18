#include "c0.h"
//T g1 i32 : p u64 u64 : i32[5,0,-3] 3 0 | i32[5,0,-3] 3 1 | i32[5,0,-3] 3 2 | i32[5,0,-3] 3 3 | i32[] 0 0
i32 g1(i32 *arr, u64 n, u64 i) { return (i < n && arr[i] > 0) ? 1 : 0; }
//T g2 bool : p u64 u64 : i32[5,0,-3] 3 0 | i32[5,0,-3] 3 1 | i32[5,0,-3] 3 3 | i32[] 0 0
bool g2(i32 *arr, u64 n, u64 i) { return i >= n || arr[i] == 0; }
//T g3 i32 : p u64 u64 : i32[5,0,-3] 3 0 | i32[5,0,-3] 3 2 | i32[5,0,-3] 3 3 | i32[] 0 0
i32 g3(i32 *arr, u64 n, u64 i) { return i < n ? arr[i] : -1; }
//T g4 i32 : p u64 u64 : i32[5,0,-3] 3 0 | i32[5,0,-3] 3 2 | i32[5,0,-3] 3 3 | i32[] 0 0
i32 g4(i32 *arr, u64 n, u64 i) { return !(i < n) ? -1 : arr[i]; }
//T g5 i32 : p u64 u64 u64 : i32[5,7,-3] 3 0 1 | i32[5,7,-3] 3 3 2 | i32[5,7,-3] 3 2 3 | i32[5,7,-3] 3 9 9
i32 g5(i32 *arr, u64 n, u64 i, u64 j) { return (i < n ? arr[i] : 0) + (j < n ? arr[j] : 0) * 10; }
//T g6 u32 : bool bool bool : 0 0 0 | 0 0 1 | 0 1 0 | 0 1 1 | 1 0 0 | 1 0 1 | 1 1 0 | 1 1 1
u32 g6(bool a, bool b, bool c) { u32 r = 0u; if (a && b || c) r += 1u; if (a || b && c) r += 2u; if (!(a && b) || !c) r += 4u; if (!(a || b) && !c) r += 8u; if ((a || b) && (b || c)) r += 16u; r += (u32)(a && b) * 32u + (u32)(a || c) * 64u; bool x = a && !b || c; r += x * 128u; return r; }
//T g7 u32 : p u64 u64 : u32[5,0,3] 3 0 | u32[5,0,3] 3 1 | u32[5,0,3] 3 3 | u32[] 0 0
u32 g7(u32 *arr, u64 n, u64 i) { u32 r = 1u; if (i < n && arr[i]) { r = r * 10u + arr[i]; } else { r = r * 100u + 7u; r += 1u; } return r; }
//T g7b u32 : p u64 u64 : u32[5,0,3] 3 0 | u32[5,0,3] 3 1 | u32[5,0,3] 3 3 | u32[] 0 0
u32 g7b(u32 *arr, u64 n, u64 i) { u32 r = 1u; if (i >= n || !arr[i]) { r = r * 100u + 7u; r += 1u; } else { r = r * 10u + arr[i]; } return r; }
//T g8 u64 : p u64 : u8[1,2,3,0,5] 5 | u8[1,2,3] 3 | u8[] 0 | u8[0] 1
u64 g8(u8 *s, u64 n) { u64 i = 0ULL; while (i < n && s[i] != 0) i++; return i; }
//T g8b u64 : p u64 : u8[1,2,3,0,5] 5 | u8[1,2,3] 3 | u8[] 0 | u8[0] 1
u64 g8b(u8 *s, u64 n) { u64 i = 0ULL; for (; !(i >= n || s[i] == 0); i++) { } return i; }
//T g8c u64 : p u64 : u8[1,2,3,0,5] 5 | u8[1,2,3] 3 | u8[0] 1
u64 g8c(u8 *s, u64 n) { u64 i = 0ULL; do { i++; } while (i < n && s[i] != 0); return i; }
static inline u32 bump(u32 *p) { p[0] = p[0] + 1u; return p[0]; }
//T g10 u32 : p : u32[0] | u32[2] | u32[3] | u32[20]
u32 g10(u32 *p) { u32 r = 0u; if (bump(p) > 3u && bump(p) < 10u) r = 1u; return r * 100u + p[0]; }
//T g10b u32 : p : u32[0] | u32[2] | u32[3] | u32[20]
u32 g10b(u32 *p) { u32 r = 0u; if (bump(p) > 3u || bump(p) > 2u) r = 1u; return r * 100u + p[0]; }
//T g10c u32 : p bool : u32[0] 0 | u32[0] 1
u32 g10c(u32 *p, bool c) { u32 r = c ? bump(p) : 77u; return r * 100u + p[0]; }
//T g10d u32 : p u32 : u32[0] 0 | u32[0] 5
u32 g10d(u32 *p, u32 n) { u32 i = 0u; while (bump(p) < n) { i += 10u; } return i + p[0]; }
//T g11 u32 : u32 u64 : 0 0 | 5 0 | 0 0x100000000 | 2 1
u32 g11(u32 x, u64 y) { return !!x + (!x == !y) * 10u + !y * 100u + (!x != 0) * 1000u + (!(x & 2u)) * 10000u; }
//T g12 u32 : u32 u32 : 0 0 | 2 0 | 0 4 | 2 4
u32 g12(u32 a, u32 b) { u32 r = a && b; u32 s = a || b; return r + s * 10u + ((a && b) + (a || b)) * 100u; }
//T g13 i32 : i32 i32 i32 : 1 0 0 | 0 1 0 | 0 0 1 | 0 0 0
i32 g13(i32 a, i32 b, i32 c) { return a ? 10 : b ? 20 : c ? 30 : 40; }
//T g14 i32 : i32 i32 : 1 1 | 1 0 | 0 1 | 0 0
i32 g14(i32 a, i32 b) { return a ? b ? 1 : 2 : b ? 3 : 4; }
//T g15 u32 : u32 u32 : 3 0 | 0 3 | 0 0
u32 g15(u32 a, u32 b) { u32 r = 0u; if (a) { if (b) r = 1u; else r = 2u; } else if (b) r = 3u; else r = 4u; return r; }
//T g16 u32 : u32 : 0 | 1 | 5
u32 g16(u32 a) { u32 r = 5u; if (a) if (a > 3u) r = 1u; else r = 2u; return r; }
