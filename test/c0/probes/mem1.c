#include "c0.h"
struct S { u8 a; u32 b; u16 c; u64 d; };
struct In { u16 x; u8 y; };
struct Out { u8 t; struct In in; u32 arr[3]; struct In ins[2]; };
typedef struct { u32 k; struct { u8 lo; u8 hi; } pr; } anon_t;
union U { u32 w; u8 b[4]; struct { u16 lo; u16 hi; } h; };
//T m1 u64 : p u32 : u8[1,2,3,4] 3 | u8[1,2,3,4] 0
u64 m1(u8 *p, u32 i) { return *(p + i); }
//T m2 u64 : p i32 : u16[1,2,3,4]+4 1 | u16[1,2,3,4]+4 -2 | u16[1,2,3,4]+4 0
u64 m2(u16 *p, i32 i) { return *(p + i) + *(i + p) * 10u + p[i] * 100u; }
//T m3 u32 : p : u32[11,22,33]+4 | u32[11,22,33]+8
u32 m3(u32 *p) { return p[-1] + *(p - 1) * 2u; }
//T m3b u64 : p i64 : u64[11,22,33]+16 -2 | u64[11,22,33] 2
u64 m3b(u64 *p, i64 i) { return p[i]; }
//T m3c u64 : p u8 : u64[11,22,33] 2 | u64[11,22,33] 0
u64 m3c(u64 *p, u8 i) { u64 *q = p + i; return *q + q[0 - i]; }
//T m3d i64 : p i8 : i16[-5,22,-33]+4 -2 | i16[-5,22,-33]+4 0
i64 m3d(i16 *p, i8 i) { return p[i]; }
//T m4 i64 : p u64 : u32[1,2,3,4,5] 3 | u32[1,2,3,4,5] 0 | u32[1,2,3,4,5] 5
i64 m4(u32 *p, u64 k) { u32 *q = p + k; return (q - p) * 1000 + (p - q) + (p < q) * 10 + (q > p) * 20 + (p <= q) * 40 + (p == q) * 80 + (p != q) * 160 + (q >= p) * 320; }
//T m4b i64 : p u64 : u64[1,2,3,4,5] 3 | u8[1,2,3,4,5] 4
i64 m4b(u64 *p, u64 k) { u8 *b = (u8 *)p; u8 *e = b + k * 8; u64 *q = (u64 *)e; return (q - p) * 100 + (e - b); }
//T m4c i64 : p u64 : u8[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] 2
i64 m4c(struct S *p, u64 k) { struct S *q = p + k; struct S *r = q - 1; return (q - p) * 100 + (r - p) * 10 + ((u8 *)q - (u8 *)p); }
//T m5 void : p u32 u64 : u8[255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] 0x11223344 0x5566778899aabbcc
void m5(struct S *p, u32 b, u64 d) { u32 *q = &p->b; *q = b; u64 *r = &p->d; r[0] = d; u16 *c = &p->c; *c = (u16)b; u8 *a = &p->a; a[0] = 7; }
//T m6 u64 : p : u8[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
u64 m6(struct S *p) { return ((u64)&p->d - (u64)p) * 1000u + ((u64)&p->c - (u64)p) * 100u + ((u64)&p->b - (u64)p) * 10u + sizeof(struct S) * 10000u + sizeof(*p) * 1000000u; }
//T m7 u64 : p : u8[1,0,2,3,4,0,0,0,5,0,0,0,6,0,0,0,7,0,0,0,8,0,9,0,10,0,11,0]
u64 m7(struct Out *p) { return p->t + p->in.x * 10u + p->in.y * 100u + p->arr[0] * 1000u + p->arr[2] * 10000u + p->ins[0].x * 100000u + p->ins[1].y * 1000000u + p->ins[1].x * 10000000ULL + sizeof(struct Out) * 1000000000ULL; }
//T m8 void : p u32 : u8[255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255,255] 0x12345678
void m8(struct Out *p, u32 v) { p->t = (u8)v; p->in.x = (u16)v; p->in.y = 1; p->arr[1] = v; p->ins[1].x = 2; p->ins[0].y = 3; struct In *q = &p->ins[1]; q->y = 4; u32 *a = p->arr; a[2] = 5u; u32 *b = &p->arr[0]; b[0] = 6u; }
//T m9 u64 : p : u32[1,2,3,4,5,6,7,8,9,10,11,12]
u64 m9(struct S *p) { struct S *q = p + 1; return q->b + p[1].c * 10u + (p + 1)->d * 100u + (*q).a * 1000u + (&p[1])->b; }
//T m10 u32 : p u32 : u32[0] 0x11223344
u32 m10(union U *p, u32 v) { p->w = v; p->b[1] = 0xee; p->h.hi = 0xabcd; return p->w + p->b[0] + p->h.lo; }
//T m11 u32 : p : u8[1,2,3,4,5,6,7,8]
u32 m11(anon_t *p) { p->pr.hi = 9; return p->k + p->pr.lo + p->pr.hi * 3u + sizeof(anon_t); }
//T m12 i64 : p : i8[-1,127,-128] | u8[200,1,2]
i64 m12(i8 *p) { return p[0] + p[1] * 2 + p[2] * 3; }
//T m13 void : p u32 : u8[9,9,9,9] 0 | u8[9,9,9,9] 256 | u8[9,9,9,9] 1
void m13(bool *p, u32 x) { p[0] = x; p[1] = !x; p[2] = x & 0x100u; p[3] = p[0] && p[2]; }
//T m14 void : p u32 : u8[9,9,9,9,9,9,9,9] 0x12345678 | u8[9,9,9,9,9,9,9,9] 0xffffff80
void m14(u8 *p, u32 x) { p[0] = x; i16 *q = (i16 *)(p + 2); q[0] = x; i8 *r = (i8 *)(p + 4); *r = x; r[1] = (i32)x >> 4; u16 *w = (u16 *)(p + 6); *w = -1; }
//T m15 void : p u32 : u8[255,1,128,7,0,0,0,128,255,255,255,255,255,255,255,127] 3
void m15(u8 *p, u32 v) { p[0] += v; p[1] -= 2; p[2] <<= 1; p[3]++; p[3]++; (*p)++; i32 *q = (i32 *)(p + 4); q[0] >>= 4; *q *= 2; i64 *r = (i64 *)(p + 8); r[0]++; *r /= -3; r[0] %= 1000; }
//T m16 u32 : p : u32[0] | u32[5]
u32 m16(u32 *p) { u32 r = 0u; if (p) r += 1u; if (!p) r += 2u; if (p == NULL) r += 4u; if (p != 0) r += 8u; if (p && p[0]) r += 16u; u32 *z = NULL; if (z == 0) r += 32u; if (!z) r += 64u; return r; }
//T m17 u32 : p : u32[1,2,3,4]
u32 m17(u32 *p) { u32 *q = p; q++; u32 a = *q; q += 2; u32 b = *q; q--; u32 c = *q; q -= 2; return a + b * 10u + c * 100u + *q * 1000u; }
//T m18 u64 : p : u8[1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16]
u64 m18(u8 *p) { u16 *a = (u16 *)p; u32 *b = (u32 *)p; u64 *c = (u64 *)p; return *(a + 1) + *(b + 1) + *(c + 1) + *(u8 *)(c + 1) + (u64)((u8 *)(b + 3) - p) + (u64)((u8 *)(a + 3) - p) * 100; }
//T m19 u32 : p : u32[7,8,9]
u32 m19(void *v) { u32 *p = (u32 *)v; u8 *b = (u8 *)v + 4; return p[2] + *(u32 *)b; }
//T m20 void : p p u64 : u8[1,2,3,4,5] u8[0,0,0,0,0] 5 | u8[] u8[] 0
void m20(const u8 *src, u8 *dst, u64 n) { for (u64 i = 0ULL; i < n; i++) { dst[n - 1 - i] = src[i]; } }
