#include "c0.h"
typedef union { struct { u32 lit:31; u32 binary:1; } b; u32 raw; } watch;
typedef struct { u8 a; u8 b; u16 c; } s4;
typedef struct { u16 x; i8 y; bool z; u32 w; } s8;
//T pk u32 : u32 bool : 5 1 | 0xffffffff 0 | 0x7fffffff 1
u32 pk(u32 lit, bool bin) { watch w = {0}; w.b.lit = lit; w.b.binary = bin; return w.raw; }
//T up u32 : u32 : 0x80000005 | 0x7fffffff
u32 up(u32 raw) { watch w = {0}; w.raw = raw; return w.b.lit * 2u + w.b.binary; }
//T l4 u32 : u32 : 0x12345678
u32 l4(u32 v) { s4 s = {0}; s.a = v; s.c = v >> 8; s.b = s.a + 1; return s.a + s.b * 256u + s.c * 65536u; }
//T l8 u64 : p : u8[1,2,0xff,1,5,6,7,8]
u64 l8(s8 *p) { s8 v = *p; v.x = v.x + 1; i32 y = v.y; return v.x + (u64)(u32)y * 3u + v.z * 5u + (u64)v.w * 7u; }
//T st8 void : p u32 : u8[0,0,0,0,0,0,0,0,9,9,9,9,9,9,9,9] 0x8765
void st8(s8 *p, u32 v) { s8 t = {0}; t.x = v; t.y = -2; t.z = v; t.w = v * 3u; p[1] = t; *p = p[1]; p->y = 1; }
