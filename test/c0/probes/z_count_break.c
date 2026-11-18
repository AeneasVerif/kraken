#include "c0.h"
//T common u32 : p u32 p u32 : u32[1,2,3,4] 4 u32[9,3,1] 3 | u32[1] 1 u32[1] 1 | u32[] 0 u32[] 0
u32 common(u32 *a, u32 n, u32 *b, u32 m) { u32 count = 0u; for (u32 i = 0u; i < n; i++) { for (u32 j = 0u; j < m; j++) { if (a[i] == b[j]) { count++; break; } } } return count; }
//T lastmatch u32 : p u32 : u32[0,5,0,7,0] 5 | u32[0,0] 2
u32 lastmatch(u32 *a, u32 n) { u32 last = 99u; u32 i = 0u; while (i < n) { u32 k = 0u; while (k < 3u) { if (a[i] != 0u) { last = i; break; } k++; } i++; } return last; }
//T state u32 : p u32 : u8[1,2,3,1,2] 5 | u8[3] 1
u32 state(u8 *a, u32 n) { u32 st = 0u; u32 acc = 0u; for (u32 i = 0u; i < n; i++) { switch (a[i]) { case 1: { st = 1u; break; } case 2: { if (st == 1u) { st = 2u; break; } st = 0u; break; } default: { st = 7u; break; } } acc = acc * 10u + st; } return acc; }
