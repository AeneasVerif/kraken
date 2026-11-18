#include "c0.h"
struct A { u8 t; u32 arr[3]; u16 w[5]; };
//T f u64 : p : u32[0,0,0,0,0,0,0]
u64 f(struct A *p) { return sizeof(p->arr) * 100u + sizeof(p->arr) / sizeof(p->arr[0]) * 10u + sizeof(p->w) / sizeof(u16); }
