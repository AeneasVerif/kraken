#include "c0.h"
//T h25 u32 : u32 : 0 | 1 | 5
u32 h25(u32 a) { u32 r = 0u; { if (a == 0u) goto skip; return 5u; skip: r = 3u; } return r; }
