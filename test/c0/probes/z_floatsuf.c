#include "c0.h"
//T a f64 : :
f64 a(void) { return 0.1f; }
//T b f64 : :
f64 b(void) { return 1.0f / 3.0f; }
//T c f64 : f64 : 3.0
f64 c(f64 x) { return x * 0.1F + 16777217.0f; }
