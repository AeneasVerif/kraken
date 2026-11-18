#include "c0.h"
//T a u64 : :
u64 a(void) { return 0xFFFFFFFFFFFFFFFF >> 1; }
//T b u64 : :
u64 b(void) { return 0x8000000000000000 / 2; }
//T c bool : i64 : -1 | 5
bool c(i64 x) { return x < 0x8000000000000000; }
//T d bool : :
bool d(void) { return 0xFFFFFFFFFFFFFFFF > 0; }
//T e u64 : :
u64 e(void) { return 0xFFFFFFFF00000000 >> 4; }
//T f u64 : :
u64 f(void) { return 0x7FFFFFFFFFFFFFFF >> 4; }
//T g bool : :
bool g(void) { return -1 < 0x100000000; }
