#include "c0.h"
struct P { u32 x; u32 y; };
//T f u32 : p : u32[4,5]
u32 f(struct P *p) { struct P v = *p; v.x += 1u; return v.x + v.y; }
