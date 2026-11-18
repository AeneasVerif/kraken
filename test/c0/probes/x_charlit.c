#include "c0.h"
//T a i32 : :
i32 a(void) { return '\xff'; }
//T b bool : i8 : -1 | 127
bool b(i8 c) { return c == '\xff'; }
