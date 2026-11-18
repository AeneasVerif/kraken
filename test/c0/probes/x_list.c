#include "c0.h"
struct N { u32 v; struct N *next; };
//T sum u32 : p : u8[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
u32 sum(struct N *p) { p[0].v = 3u; p[0].next = &p[2]; p[2].v = 40u; p[2].next = p + 1; p[1].v = 500u; p[1].next = NULL; u32 s = 0u; u32 k = 0u; struct N *q = p; while (q) { s += q->v * (k + 1u); k++; q = q->next; } u32 t = p->next->next->v; struct N **pp = &p->next; return s + t * 10000u + (*pp)->v * 1000000u; }
