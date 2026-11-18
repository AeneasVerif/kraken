#include "c0.h"
//T f u32 : u32 : 0 | 1
u32 f(u32 x) { switch (x) { case 0: return 1u; default: return 2u; } }
