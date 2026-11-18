#include "c0.h"
typedef C0_RET2(u32, u32) pr;
static inline pr step(u32 a, u32 b) { return C0_TUP2(pr, b, a + b); }
//T fib u32 : u32 : 0 | 1 | 10
u32 fib(u32 n) { u32 a = 0u; u32 b = 1u; for (u32 i = 0u; i < n; i++) { C0_TIE2(a, b, step(a, b)); } return a; }
//T fib2 u32 : u32 : 0 | 1 | 10
u32 fib2(u32 n) { u32 a = 0u; u32 b = 1u; u32 i = 0u; while (i < n) { if (i & 1u) { C0_TIE2(a, b, step(a, b)); } else { C0_TIE2(a, b, step(a, b)); i++; continue; } i++; } return a; }
