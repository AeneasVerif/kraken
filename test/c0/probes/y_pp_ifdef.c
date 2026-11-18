#include "c0.h"
//T f u32 : u32 : 5
u32 f(u32 x) {
#ifdef NOT_DEFINED_ANYWHERE
  x += 1000u;
#endif
#if 0
  x += 100u;
#else
  x += 10u;
#endif
  return x;
}
