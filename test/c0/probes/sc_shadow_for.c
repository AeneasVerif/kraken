#include "c0.h"
//T i3 u32 : u32 : 0 | 4
u32 i3(u32 n) { u32 i = 77u; u32 s = 0u; for (u32 i = 0u; i < n; i++) { s += i; } return i * 1000u + s; }
