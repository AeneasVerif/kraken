#include "c0.h"
//T h1 u32 : u32 : 0 | 1 | 5 | 10
u32 h1(u32 n) { u32 s = 0u; for (u32 i = 0u; i < n; i++) { if ((i & 1u) == 0u) continue; s += i; } return s; }
//T h2 u32 : u32 : 0 | 1 | 2 | 5 | 6
u32 h2(u32 n) { u32 i = 0u; u32 s = 0u; do { i++; if (i & 1u) continue; s += i; } while (i < n); return s * 100u + i; }
//T h2w u32 : u32 : 0 | 1 | 2 | 5 | 6
u32 h2w(u32 n) { u32 i = 0u; u32 s = 0u; while (i < n) { i++; if (i & 1u) continue; s += i; } return s * 100u + i; }
//T h3 u32 : p u32 : u32[0,1,2,3,4,0,2] 7 | u32[] 0 | u32[2] 1 | u32[9,9] 2
u32 h3(u32 *a, u32 n) { u32 s = 0u; for (u32 i = 0u; i < n; i++) { switch (a[i]) { case 0: continue; case 1: s += 1u; break; case 2: s += 10u; fallthrough; case 3: s += 100u; break; default: s += 1000u; break; } s += 10000u; } return s; }
//T h4 u32 : u32 : 0 | 1 | 2 | 77
u32 h4(u32 v) { u32 r = 0u; switch (v) { case 0: r = 1u; break; default: r = 9u; break; case 1: r = 2u; break; } return r; }
//T h9 u32 : u32 : 0xff | 0xfe | 1 | 0x80 | 0x180
u32 h9(u32 x) { u32 r = 0u; switch ((i8)x) { case -1: r = 1u; break; case -2: r = 2u; break; case 1: r = 3u; break; case -128: r = 4u; break; default: r = 5u; break; } return r; }
//T h9b u32 : u64 : 0x100000000 | 0 | 1 | 0xffffffffffffffff
u32 h9b(u64 x) { u32 r = 0u; switch (x) { case 0x100000000: r = 1u; break; case 0: r = 2u; break; case -1: r = 3u; break; default: r = 5u; break; } return r; }
//T h9c u32 : u8 : 0 | 255 | 44
u32 h9c(u8 x) { u32 r = 0u; switch (x) { case 0: r = 2u; break; case 255: r = 3u; break; case 300: r = 4u; break; default: r = 5u; break; } return r; }
//T h10 u32 : u32 : 0 | 1 | 2 | 3 | 4
u32 h10(u32 v) { switch (v) { case 0: return 10u; case 1: case 2: return 20u; case 3: v = v + 100u; break; } return v; }
//T h11 u32 : u32 u32 : 0 0 | 0 1 | 1 0 | 1 1 | 2 2
u32 h11(u32 a, u32 b) { u32 r = 0u; switch (a) { case 0: switch (b) { case 0: r = 1u; break; default: r = 2u; break; } r += 10u; break; case 1: switch (b) { case 0: r = 3u; break; case 1: r = 4u; break; } r += 20u; break; default: r = 99u; break; } return r; }
//T h13 u32 : u32 u32 : 0 0 | 3 3 | 5 4 | 4 7
u32 h13(u32 n, u32 m) { u32 s = 0u; for (u32 i = 0u; i < n; i++) { for (u32 j = 0u; j < m; j++) { if (j > i) break; if ((i + j) % 3u == 0u) continue; s += i * j + 1u; } s += 1000u; } return s; }
//T h14 u32 : p u32 u32 u32 : u32[1,2,3,4,5,6] 2 3 5 | u32[1,2,3,4,5,6] 2 3 1 | u32[1,2,3,4,5,6] 2 3 9 | u32[1,2,3,4,5,6] 3 2 6
u32 h14(u32 *a, u32 n, u32 m, u32 t) { for (u32 i = 0u; i < n; i++) { for (u32 j = 0u; j < m; j++) { if (a[i * m + j] == t) return i * 100u + j; } } return 0xffffffffu; }
static inline u32 find(u32 *a, u32 n, u32 t) { for (u32 i = 0u; i < n; i++) { if (a[i] == t) return i; } return n; }
//T h15 u32 : p u32 p u32 : u32[5,6,7] 3 u32[7,5,9,6] 4 | u32[5,6,7] 3 u32[] 0
u32 h15(u32 *a, u32 n, u32 *ts, u32 k) { u32 s = 0u; for (u32 j = 0u; j < k; j++) { s = s * 10u + find(a, n, ts[j]); } return s; }
//T h16 u32 : p u32 u32 u32 : u32[1,2,3,4,5,6] 2 3 5 | u32[1,2,3,4,5,6] 2 3 1 | u32[1,2,3,4,5,6] 2 3 9
u32 h16(u32 *a, u32 n, u32 m, u32 t) { u32 r = 0u; u32 cnt = 0u; for (u32 i = 0u; i < n; i++) { for (u32 j = 0u; j < m; j++) { cnt++; if (a[i * m + j] == t) { r = i * 100u + j; goto done; } } } r = 7777u; done: return r + 1u + cnt * 10000u; }
//T h17 u32 : u32 : 0 | 1 | 17 | 100
u32 h17(u32 n) { u32 i = 0u; for (;;) { if (i * i >= n) return i; i++; } }
//T h22 u32 : u32 : 0 | 1 | 255 | 256 | 0x80000000
u32 h22(u32 n) { u32 c = 0u; while (n) { n >>= 1; c++; } return c; }
//T h23 u32 : u32 : 0 | 1 | 5
u32 h23(u32 n) { u32 s = 0u; for (u32 i = n; i > 0u; i--) { s = s * 10u + i; } return s; }
//T h24 u32 : u32 : 0 | 1 | 5
u32 h24(u32 n) { u32 s = 0u; u32 i = 0u; do { s += i; i++; } while (0); do { s += 100u; if (s > n) break; s += 1000u; } while (i < 0u); return s + i; }
