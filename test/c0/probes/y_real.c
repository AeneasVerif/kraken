#include "c0.h"
//T isort void : p u32 : u32[5,2,9,1,5,6] 6 | u32[] 0 | u32[3] 1 | u32[2,1] 2
void isort(u32 *a, u32 n) { for (u32 i = 1u; i < n; i++) { u32 key = a[i]; u32 j = i; while (j > 0u && a[j - 1u] > key) { a[j] = a[j - 1u]; j--; } a[j] = key; } }
//T bsearch_ i32 : p u32 u32 : u32[1,3,5,7,9] 5 7 | u32[1,3,5,7,9] 5 1 | u32[1,3,5,7,9] 5 4 | u32[] 0 4 | u32[1,3,5,7,9] 5 9
i32 bsearch_(u32 *a, u32 n, u32 t) { u32 lo = 0u; u32 hi = n; while (lo < hi) { u32 mid = lo + (hi - lo) / 2u; if (a[mid] == t) return (i32)mid; if (a[mid] < t) lo = mid + 1u; else hi = mid; } return -1; }
//T gcd u64 : u64 u64 : 12 18 | 17 5 | 0 9 | 9 0
u64 gcd(u64 a, u64 b) { while (b != 0ULL) { u64 t = a % b; a = b; b = t; } return a; }
//T crc u32 : p u64 : u8[1,2,3,4,5,6,7,8,9] 9 | u8[] 0
u32 crc(const u8 *p, u64 n) { u32 c = 0xFFFFFFFFu; for (u64 i = 0ULL; i < n; i++) { c ^= p[i]; for (u32 k = 0u; k < 8u; k++) { if (c & 1u) c = (c >> 1) ^ 0xEDB88320u; else c >>= 1; } } return ~c; }
//T sieve u32 : p u32 : u8[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] 30
u32 sieve(u8 *s, u32 n) { u32 cnt = 0u; for (u32 i = 2u; i < n; i++) { if (s[i]) continue; cnt++; for (u32 j = i * i; j < n; j += i) s[j] = 1; } return cnt; }
//T memcmp_ i32 : p p u64 : u8[1,2,3] u8[1,2,4] 3 | u8[1,2,3] u8[1,2,3] 3 | u8[200] u8[100] 1 | u8[] u8[] 0
i32 memcmp_(const u8 *a, const u8 *b, u64 n) { for (u64 i = 0ULL; i < n; i++) { if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1; } return 0; }
//T atoi_ i32 : p : u8[32,32,45,49,50,51,0] | u8[52,50,120,0] | u8[0] | u8[43,55,0]
i32 atoi_(const char *s) { u32 i = 0u; while (s[i] == ' ') i++; bool neg = false; if (s[i] == '-') { neg = true; i++; } else if (s[i] == '+') { i++; } i32 v = 0; while (s[i] >= '0' && s[i] <= '9') { v = v * 10 + (s[i] - '0'); i++; } return neg ? -v : v; }
//T collatz u32 : u64 : 1 | 6 | 27
u32 collatz(u64 n) { u32 steps = 0u; while (n != 1ULL) { if (n & 1ULL) n = 3ULL * n + 1ULL; else n >>= 1; steps++; } return steps; }
//T matmul void : p p p : i32[1,2,3,4] i32[5,6,7,8] i32[0,0,0,0]
void matmul(const i32 *a, const i32 *b, i32 *c) { for (u32 i = 0u; i < 2u; i++) { for (u32 j = 0u; j < 2u; j++) { i32 s = 0; for (u32 k = 0u; k < 2u; k++) { s += a[i * 2u + k] * b[k * 2u + j]; } c[i * 2u + j] = s; } } }
//T firstdup i32 : p u32 : u32[1,2,3,2,1] 5 | u32[1,2,3] 3 | u32[] 0
i32 firstdup(u32 *a, u32 n) { i32 res = -1; for (u32 i = 0u; i < n; i++) { bool dup = false; for (u32 j = 0u; j < i; j++) { if (a[j] == a[i]) { dup = true; break; } } if (dup) { res = (i32)i; break; } } return res; }
//T count_classes u32 : p u32 : u8[0,1,2,3,1,1,0,9] 8 | u8[] 0
u32 count_classes(u8 *a, u32 n) { u32 z = 0u; u32 o = 0u; u32 other = 0u; u32 i = 0u; while (i < n) { if (a[i] == 0) { z++; i++; continue; } if (a[i] == 1) { o++; } else { other += a[i]; } i++; } return z + o * 10u + other * 100u; }
//T popcnt_table u32 : u32 : 0 | 0xff | 0x80000001
u32 popcnt_table(u32 x) { u32 c = 0u; do { c += x & 1u; x >>= 1; } while (x != 0u); return c; }
//T maxrun u32 : p u32 : u8[1,1,2,2,2,3,2,2] 8 | u8[] 0 | u8[7] 1
u32 maxrun(u8 *a, u32 n) { u32 best = 0u; u32 i = 0u; while (i < n) { u32 j = i; while (j < n && a[j] == a[i]) { j++; } if (j - i > best) { best = j - i; } i = j; } return best; }
//T findpair u32 : p u32 u32 : u32[1,4,6,9] 4 10 | u32[1,4,6,9] 4 3 | u32[] 0 1
u32 findpair(u32 *a, u32 n, u32 t) { u32 res = 0u; for (u32 i = 0u; i < n; i++) { for (u32 j = i + 1u; j < n; j++) { if (a[i] + a[j] == t) { res = i * 16u + j + 1u; goto out; } } } out: return res; }
//T utf8len u32 : p u32 : u8[0x41,0xc3,0xa9,0xe2,0x82,0xac,0x42] 7
u32 utf8len(const u8 *s, u32 n) { u32 cnt = 0u; for (u32 i = 0u; i < n; i++) { switch (s[i] >> 6) { case 2: continue; default: cnt++; break; } } return cnt; }
//T tokens u32 : p u32 : u8[32,97,98,32,32,99,32] 7 | u8[97] 1 | u8[] 0
u32 tokens(const u8 *s, u32 n) { u32 cnt = 0u; bool in = false; for (u32 i = 0u; i < n; i++) { if (s[i] == ' ') { in = false; continue; } if (!in) { cnt++; in = true; } } return cnt; }
//T lastidx i32 : p u32 u32 : u32[1,2,1,3] 4 1 | u32[1,2,1,3] 4 7
i32 lastidx(u32 *a, u32 n, u32 t) { i32 r = -1; for (u32 i = 0u; i < n; i++) { for (u32 k = 0u; k < 1u; k++) { if (a[i] != t) { break; } r = (i32)i; } } return r; }
