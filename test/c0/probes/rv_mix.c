#include "c0.h"
#define LIM 3u
#define HAVE_A 1
struct S { i32 s:5; u32 u:3; i32 w:24; };

//T tri u32 : p u32 :  u32[1,2,3,4,5,6,7,8] 8 | u32[5,5,5,5,5,5,5,5] 8 | u32[0,9,0,9,0,9,0,9] 8 | u32[1,2,3,4,5,6,7,8] 0
u32 tri(u32 *a, u32 n) {
  u32 hits = 0u; u32 last = 77u;
  for (u32 i = 0u; i < n; i++) {
    for (u32 j = 0u; j < n; j++) {
      if (a[j] > a[i]) { last = j; break; }
      for (u32 k = 0u; k < LIM; k++) {
        if (a[i] == k + j) { hits = hits + 1u; break; }
        if (k == 1u) continue;
        hits = hits + 100u;
      }
    }
  }
  return hits * 1000u + last;
}

//T wsw u32 : p u32 : u32[0,1,2,3,4,1,0,2] 8 | u32[3,3,3,3] 4 | u32[4,0,0,0] 4 | u32[2,2,1,1] 4
u32 wsw(u32 *a, u32 n) {
  u32 i = 0u; u32 acc = 0u; u32 odd = 0u;
  while (i < n) {
    u32 v = a[i];
    i = i + 1u;
    switch (v) {
      case 0: acc = acc + 1u;
      case 1: acc = acc * 3u; continue;
      case 2: { u32 acc2 = acc + 5u; acc = acc2; }
      default: odd = odd + v; break;
      case 4: return acc + 9999u;
    }
    acc = acc + 7u;
  }
  return acc * 100u + odd;
}

//T dw u32 : u32 : 0 | 1 | 2 | 5 | 9
u32 dw(u32 n) {
  u32 i = 0u; u32 s = 0u;
  do {
    i = i + 1u;
    if ((i & 1u) != 0u) continue;
    if (i > 6u) break;
    s = s + i;
  } while (i < n);
  return s * 100u + i;
}

//T shd u32 : u32 u32 : 0 5 | 1 5 | 7 0 | 3 3
u32 shd(u32 a, u32 b) {
  u32 x = a;
  u32 r = 0u;
  for (u32 i = 0u; i < b; i++) {
    u32 t = x;
    { u64 x = 1000ULL; x = x + (u64)i; r = r + (u32)x; }
    if (i == 2u) { u32 x = 5u; r = r + x; } else { x = x + 1u; }
    r = r + t;
  }
  return r * 10u + x;
}

//T tn i64 : u32 i32 u8 : 0 -5 200 | 1 -5 200 | 2 -5 200 | 3 7 0
i64 tn(u32 sel, i32 a, u8 b) {
  u64 big = 0x1122334455667788ULL;
  i64 r = sel == 0u ? a : sel == 1u ? b : sel == 2u ? big : 0;
  return r;
}

//T lit u64 : u32 : 0 | 1 | 2 | 3 | 4 | 5 | 6
u64 lit(u32 k) {
  if (k == 0u) return 0x80000000;
  if (k == 1u) return 2147483648;
  if (k == 2u) return -2147483648;
  if (k == 3u) return ~0u >> 1;
  if (k == 4u) return 1u << 31;
  if (k == 5u) return -1 < 0x80000000 ? 1ULL : 2ULL;
  return 0xFFFFFFFFu + 1;
}

//T bfs i64 : p i32 : u8[0,0,0,0] -1 | u8[0,0,0,0] 15 | u8[0,0,0,0] 16 | u8[255,255,255,255] 0 | u8[0,0,0,0] -16
i64 bfs(struct S *p, i32 v) {
  p->s = v;
  p->w = v * 1000;
  p->s -= 1;
  i64 r = p->s;
  if (p->s < 0) r = r * 10;
  if (p->u - 1 < 0) r = r + 3;
  return r * 100000 + p->w;
}

//T pp u32 : u32 : 0 | 4
u32 pp(u32 x) {
#if defined(HAVE_A) && !defined(HAVE_B)
  x = x + 1u;
#else
  x = x + 100u;
#endif
#ifdef HAVE_B
  x = x + 1000u;
#elif HAVE_A
  x = x + 20u;
#else
  x = x + 300u;
#endif
#ifndef HAVE_A
  x = x + 5000u;
#endif
  return x;
}

//T gl u32 : p u32 : u32[0,0,7,0] 4 | u32[1,0,0,0] 4 | u32[0,0,0,0] 4 | u32[0,0,0,0] 0
u32 gl(u32 *p, u32 n) {
  u32 i = 0u; u32 z = 0u;
  while (i < n) {
    if (p[i] == 0u) goto next;
    return i * 10u + z;
  next:
    z = z + 1u;
    i = i + 1u;
  }
  return 1000u + z;
}
