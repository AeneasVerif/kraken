#include "c0.h"
static inline u32 g(u32 n) { if (n == 0u) return 1u; return n * g(n - 1u); }
//T f u32 : u32 : 5
u32 f(u32 n) { return g(n); }
