#include "c0.h"
struct M { u8 m[3][4]; u16 k; };
//T f u32 : p : u8[0,1,2,3,4,5,6,7,8,9,10,11,12,13]
u32 f(struct M *p) { return p->m[1][2] + p->m[2][3] * 100u + p->k; }
