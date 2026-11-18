#include "c0.h"
static inline u32 bump(u32 *p) { p[0] = p[0] + 1u; return p[0]; }
static inline u32 sub2(u32 a, u32 b) { return a - b; }
u32 sub2n(u32 a, u32 b) { return a - b; }
u32 bumpn(u32 *p) { p[0] = p[0] * 2u; return p[0]; }
//T k1 u32 : p : u32[5]
u32 k1(u32 *p) { return sub2(bump(p), bump(p)); }
//T k1n u32 : p : u32[5]
u32 k1n(u32 *p) { return sub2n(bumpn(p), bump(p)); }
//T k3 u32 : p : u32[5]
u32 k3(u32 *p) { return bump(p) * 10u + bump(p); }
//T k3b u32 : p : u32[5]
u32 k3b(u32 *p) { return bump(p) - bumpn(p); }
//T k3c u32 : p : u32[5,0]
u32 k3c(u32 *p) { p[bump(p) - 6u] = bumpn(p); return p[0] + p[1]; }
