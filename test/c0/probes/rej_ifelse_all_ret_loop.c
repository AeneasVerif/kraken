#include "c0.h"
//T f u32 : u32 : 1 | 0 | 7
u32 f(u32 x) { for (u32 i = 0u; i < 10u; i++) { if (i == x) { return i + 100u; } else if (i > 5u) { return 7u; } } return 0u; }
