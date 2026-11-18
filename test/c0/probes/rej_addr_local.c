#include "c0.h"
//T f u32 : u32 : 5
u32 f(u32 x) { u32 y = x; u32 *p = &y; *p = 7u; return y; }
