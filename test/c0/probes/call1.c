#include "c0.h"
typedef C0_RET2(u32, u32) pr;
typedef C0_RET2(i32, bool) ib;
typedef C0_RET3(u8, i16, u64) t3;
static inline u32 bump(u32 *p) { p[0] = p[0] + 1u; return p[0]; }
static inline u32 sub2(u32 a, u32 b) { return a - b; }
static inline pr dm(u32 a, u32 b) { return C0_TUP2(pr, a / b, a % b); }
//T dm2 (u32,u32) : u32 u32 : 17 5 | 0 3
pr dm2(u32 a, u32 b) { return C0_TUP2(pr, a / b, a % b); }
//T k2 u32 : p : u32[5]
u32 k2(u32 *p) { u32 a = bump(p); u32 b = bump(p); return a * 10u + b; }
//T k6 u32 : u32 u32 : 17 5 | 0 3
u32 k6(u32 a, u32 b) { u32 q = 0u; u32 r = 0u; C0_TIE2(q, r, dm(a, b)); return q * 1000u + r; }
//T k6b u32 : u32 u32 : 17 5 | 0 3
u32 k6b(u32 a, u32 b) { u32 q = 0u; u32 r = 0u; C0_TIE2(q, r, dm2(a, b)); return q * 1000u + r; }
//T k7 u64 : u32 u32 : 1000 3 | 7 1000
u64 k7(u32 a, u32 b) { u8 q = 0; u64 r = 0ULL; C0_TIE2(q, r, dm(a, b)); return q * 100000ULL + r; }
static inline ib sg(i32 a) { return C0_TUP2(ib, a - 10, a); }
//T k8 i64 : i32 : 3 | 256 | 0 | 10
i64 k8(i32 a) { i64 v = 0; u32 f = 7u; C0_TIE2(v, f, sg(a)); return v * 10 + f; }
static inline pr swp(u32 a, u32 b) { return C0_TUP2(pr, b, a); }
//T k9 u32 : u32 u32 : 1 2
u32 k9(u32 a, u32 b) { C0_TIE2(a, b, swp(a, b)); C0_TIE2(a, b, swp(a + 5u, b)); return a * 100u + b; }
static inline t3 mk3(u64 x) { return C0_TUP3(t3, x, x >> 8, x * 2ULL); }
//T k10 u64 : u64 : 0xfedcba9876543210 | 0x80ff
u64 k10(u64 x) { u8 a = 0; i16 b = 0; u64 c = 0ULL; C0_TIE3(a, b, c, mk3(x)); i64 bw = b; return a + (u64)bw * 3u + c; }
//T mk3n (u8,i16,u64) : u64 : 0xfedcba9876543210
t3 mk3n(u64 x) { return C0_TUP3(t3, x, x >> 8, x * 2ULL); }
static inline u32 clampi(u32 x, u32 lo, u32 hi) { if (x < lo) return lo; if (x > hi) { return hi; } return x; }
//T k11 u32 : u32 : 0 | 5 | 50 | 500
u32 k11(u32 x) { u32 s = 0u; for (u32 i = 0u; i < 3u; i++) { s = s * 100u + clampi(x + i, 3u, 60u); } return s; }
static inline void setmax(u32 *p, u32 v) { if (p[0] >= v) return; p[0] = v; }
//T k12 void : p u32 : u32[5] 3 | u32[5] 9
void k12(u32 *p, u32 v) { setmax(p, v); setmax(p, v + 1u); }
static inline u32 modp(u32 x) { x = x + 1u; x *= 2u; return x; }
//T k13 u32 : u32 : 5
u32 k13(u32 x) { u32 y = modp(x); return x * 100u + y + modp(modp(y)); }
static inline u8 narrow(u32 x) { return x; }
static inline i8 narrows(u32 x) { return x; }
static inline u64 widen(i32 x) { return x; }
static inline u32 takes8(u8 x, i8 y, bool z) { return x + y * 1000 + z * 100000u; }
//T k14 u64 : u32 : 0x1ff | 0x80 | 256
u64 k14(u32 x) { return narrow(x) + narrows(x) * 2 + widen(narrows(x)) + takes8(x, x, x); }
//T k15 u64 : i32 : -1 | 256
u64 k15(i32 x) { return widen(x) + takes8(-1, 200, 256); }
static inline bool isodd(u32 x) { return x & 1u; }
static inline bool big(u32 x) { return x & 0x100u; }
//T k16 u32 : u32 : 0x101 | 0x100 | 3 | 4
u32 k16(u32 x) { u32 r = 0u; if (isodd(x) && big(x)) r += 1u; if (isodd(x) || big(x)) r += 2u; r += big(x) * 4u; while (!isodd(x)) { x++; r += 8u; } return r + (big(x) ? 16u : 32u); }
static inline u32 depth3(u32 x) { return x + 1u; }
static inline u32 depth2(u32 x) { if (x > 10u) return depth3(x) * 2u; return depth3(x); }
static inline u32 depth1(u32 x) { u32 s = 0u; for (u32 i = 0u; i < x; i++) { s += depth2(i * 5u); if (s > 40u) return s; } return s + 1000u; }
//T k17 u32 : u32 : 0 | 2 | 5 | 9
u32 k17(u32 x) { return depth1(x) + depth1(x + 1u) * 3u; }
static inline u32 loopret(u32 *a, u32 n) { u32 i = 0u; while (i < n) { if (a[i] == 0u) return i; i++; } return n; }
//T k18 u32 : p u32 : u32[1,2,0,4] 4 | u32[1,2] 2 | u32[] 0
u32 k18(u32 *a, u32 n) { u32 x = loopret(a, n); u32 y = 0u; if (x < n) { y = loopret(a + x + 1, n - x - 1u); } return x * 10u + y; }
static inline u32 two_tail(u32 x) { if (x & 1u) { return x * 3u; } else { return x / 2u; } }
//T k19 u32 : u32 : 5 | 6
u32 k19(u32 x) { u32 r = two_tail(x); r += two_tail(r); return r; }
static inline u32 inl_sw(u32 x) { switch (x) { case 0: return 5u; case 1: x += 7u; break; default: return 9u; } return x; }
//T k20 u32 : u32 : 0 | 1 | 2
u32 k20(u32 x) { return inl_sw(x) * 10u + inl_sw(x + 1u); }
static inline u32 inl_goto(u32 x) { u32 r = 1u; if (x > 3u) goto out; r = 2u; out: return r + x; }
//T k21 u32 : u32 : 0 | 5
u32 k21(u32 x) { u32 r = 0u; for (u32 i = 0u; i < 2u; i++) { r = r * 100u + inl_goto(x + i * 4u); } return r; }
static inline u32 inl_shadow(u32 r) { u32 s = r + 1u; return s; }
//T k22 u32 : u32 : 5
u32 k22(u32 x) { u32 r = 100u; u32 s = 200u; u32 t = inl_shadow(x); return r + s + t; }
//T k23 u32 : u32 : 5 | 0
u32 k23(u32 x) { check(x != 99u); u32 r = x; check(r < 100u); return r + 1u; }
