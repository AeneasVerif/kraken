#include "c0.h"
//T f u32 : u32 : 5
u32 f(u32 n) { u32 i = 0u; again: i++; if (i < n) goto again; return i; }
