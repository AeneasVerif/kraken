#include "c0.h"
u32 odd(u32 n);
u32 even(u32 n) { if (n == 0u) return 1u; return odd(n - 1u); }
u32 odd(u32 n) { if (n == 0u) return 0u; return even(n - 1u); }
//T f u32 : u32 : 5 | 4
u32 f(u32 n) { return even(n); }
