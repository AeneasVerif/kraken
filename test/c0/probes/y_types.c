#include "c0.h"
typedef u32 *u32p;
typedef struct P2 { u16 a; u16 b; } P2;
typedef P2 *P2p;
typedef u64 word;
typedef word dword;
//T f u32 : p : u32[4,5]
u32 f(u32p p) { u32p q = p + 1; dword s = *q; P2p r = (P2p)p; return (u32)s + r->a * 10u + r[1].b + sizeof(P2) * 100u + sizeof(dword) * 1000u; }
