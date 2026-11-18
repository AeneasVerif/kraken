#include "c0.h"
//T f u64 : u32 : 1
u64 f(u32 x) { u16 y = (u16)x; return sizeof y + sizeof(y) * 10u + sizeof(u64 *) * 100u + sizeof(x + y) * 1000u; }
