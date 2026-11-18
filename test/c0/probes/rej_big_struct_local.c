#include "c0.h"
struct P { u64 x; u64 y; };
//T f u64 : p : u64[4,5]
u64 f(struct P *p) { struct P v = *p; return v.x + v.y; }
