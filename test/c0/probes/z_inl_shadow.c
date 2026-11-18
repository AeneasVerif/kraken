#include "c0.h"
static inline u32 g(u32 x) { u32 r = x; { u32 x = 50u; r += x; } return r + x; }
//T f u32 : u32 : 1
u32 f(u32 a) { return g(a); }
