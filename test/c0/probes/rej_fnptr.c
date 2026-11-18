#include "c0.h"
u32 g(u32 x) { return x + 1u; }
//T f u32 : u32 : 0
u32 f(u32 i) { u32 (*fp)(u32) = g; return fp(i); }
