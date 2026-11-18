#include "c0.h"
//T f u64 : p : u64[0,0,7,9]
u64 f(u64 *b) { u64 **pp = (u64 **)b; pp[0] = b + 2; pp[1] = &b[3]; u64 *q = *pp; u64 *r = pp[1]; return **pp + *pp[1] * 10u + q[1] * 100u + r[-1] * 1000u + (u64)(pp[1] - pp[0]) * 10000u; }
