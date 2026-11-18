#include "c0.h"
//T f u32 : bool bool bool bool : 0 0 0 0 | 0 0 0 1 | 0 0 1 0 | 0 0 1 1 | 0 1 0 0 | 0 1 0 1 | 0 1 1 0 | 0 1 1 1 | 1 0 0 0 | 1 0 0 1 | 1 0 1 0 | 1 0 1 1 | 1 1 0 0 | 1 1 0 1 | 1 1 1 0 | 1 1 1 1
u32 f(bool a, bool b, bool c, bool d) { u32 r = 0u; u32 s = 1u;
  if ((a && b) || (c && d)) { r += 1u; s *= 2u; } else { r += 2u; s *= 3u; }
  if (!(a && (b || c))) { r += 10u; s += 1u; } else { r += 20u; s += 2u; }
  if ((a || b) && (c || d) && !(a && d)) { r += 100u; } else { r += 200u; s *= 5u; }
  if (a || (b && (c || d))) { r += 1000u; } else if (!b || !c) { r += 2000u; } else { r += 3000u; }
  while ((a && !b) || (c && s < 100u)) { s += 37u; if (s > 200u) break; a = !a; }
  return r + s * 10000u + ((a && b) || (!c && d) ? 5u : 7u) * 100000000u; }
