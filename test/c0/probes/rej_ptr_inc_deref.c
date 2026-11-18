#include "c0.h"
//T f u32 : p : u32[4,5]
u32 f(u32 *p) { u32 a = *p++; return a + *p; }
