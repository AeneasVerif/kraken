#include "c0.h"
static u32 counter = 0;
//T f u32 : u32 : 5
u32 f(u32 x) { counter += x; return counter; }
