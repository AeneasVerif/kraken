#include "c0.h"
#define SWAP(a, b) do { u32 t = a; a = b; b = t; } while (0)
//T f u32 : u32 u32 : 1 2
u32 f(u32 x, u32 y) { SWAP(x, y); return x * 10u + y; }
