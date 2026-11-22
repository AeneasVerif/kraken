/* lcnf_int_test.c: differential fuzz of lcnf_int_op (tagged small ints + sign-magnitude bignums)
 * against __int128 reference semantics (Lean Int.ediv/emod Euclidean, tdiv/tmod truncating, by
 * zero), canonical-representation and zero-leak checks. Run by test/lcnf/run.sh. */
#include "lcnf_rt.h"
#include <stdlib.h>
#include <string.h>
typedef __int128 i128;
typedef unsigned __int128 u128x;
static LcnfRt blk;
static u64 rt;
static int fails = 0;

static void dec(u64 o) {
  if (o & 1) return;
  int32_t rc; memcpy(&rc, (void *)(uintptr_t)o, 4);
  if (rc == 1) lcnf_dec_ref_cold(rt, o);
  else if (rc > 1) { rc--; memcpy((void *)(uintptr_t)o, &rc, 4); }
}
static u64 nat_of_u128(u128x v) {
  u64 lo = lcnf_nat_slow(rt, 14, (u64)v, 0);
  u64 hi = lcnf_nat_slow(rt, 14, (u64)(v >> 64), 0);
  u64 sh = lcnf_nat_slow(rt, 15, hi, (64 << 1) | 1);
  u64 r = lcnf_nat_slow(rt, 1, sh, lo);
  dec(lo); dec(hi); dec(sh);
  return r;
}
static u128x u128_of_nat(u64 n) {
  if (n & 1) return n >> 1;
  uint32_t len; memcpy(&len, (void *)(uintptr_t)(n + 12), 4);
  if (len > 2) { fprintf(stderr, "nat too big\n"); exit(2); }
  u64 lo = 0, hi = 0;
  memcpy(&lo, (void *)(uintptr_t)(n + 16), 8);
  if (len == 2) memcpy(&hi, (void *)(uintptr_t)(n + 24), 8);
  if (len == 1 && lo < (1ULL << 63)) { fprintf(stderr, "non-canonical nat\n"); fails++; }
  return ((u128x)hi << 64) | lo;
}
static u64 mk_int(i128 v) {
  u128x mag = v < 0 ? (u128x)0 - (u128x)v : (u128x)v;
  u64 n = nat_of_u128(mag);
  u64 i = lcnf_int_op(rt, 1, n, 1); /* consumes n */
  if (v < 0) { u64 j = lcnf_int_op(rt, 3, i, 1); dec(i); i = j; }
  return i;
}
static i128 rd_int(u64 x) {
  u64 z = mk_int(0);
  int neg = (int)lcnf_int_op(rt, 11, x, z);
  u64 a = lcnf_int_op(rt, 9, x, 1);
  u128x m = u128_of_nat(a);
  dec(a); dec(z);
  /* canonical small check */
  i128 v = neg ? -(i128)m : (i128)m;
  int small = v >= -((i128)1 << 62) && v < ((i128)1 << 62);
  if (small != (int)(x & 1)) { fprintf(stderr, "non-canonical int\n"); fails++; }
  return v;
}
static u64 rnd64(void) { return ((u64)rand() << 42) ^ ((u64)rand() << 21) ^ (u64)rand(); }
static i128 rnd_val(int bits) {
  int k = rand() % 8;
  i128 v;
  switch (k) {
    case 0: v = (i128)(rand() % 21) - 10; break;
    case 1: v = ((i128)1 << 62) + (rand() % 5) - 2; break;
    case 2: v = -((i128)1 << 62) + (rand() % 5) - 2; break;
    case 3: v = ((i128)1 << 63) + (rand() % 5) - 2; break;
    case 4: v = (i128)(int64_t)rnd64(); break;
    default: v = (i128)(((u128x)rnd64() << 64) | rnd64()); break;
  }
  if (bits < 127) { i128 lim = (i128)1 << bits; v %= lim; }
  if (rand() & 1) v = -v;
  return v;
}
#define CHECK(name, got, exp) do { i128 g_ = (got), e_ = (exp); if (g_ != e_) { \
  fprintf(stderr, "FAIL %s a=%lld.. b=%lld..\n", name, (long long)a, (long long)b); \
  fails++; } } while (0)

int main(void) {
  rt = (u64)(uintptr_t)&blk;
  lcnf_rt_init(rt);
  srand(12345);
  for (int it = 0; it < 100000; it++) {
    i128 a = rnd_val(it % 3 == 0 ? 62 : 125), b = rnd_val(it % 2 ? 62 : 125);
    if (it % 17 == 0) b = 0;
    u64 x = mk_int(a), y = mk_int(b);
    if (rd_int(x) != a || rd_int(y) != b) { fprintf(stderr, "roundtrip\n"); fails++; }
    u64 r;
    r = lcnf_int_op(rt, 4, x, y); CHECK("add", rd_int(r), a + b); dec(r);
    r = lcnf_int_op(rt, 5, x, y); CHECK("sub", rd_int(r), a - b); dec(r);
    i128 sa = a % ((i128)1 << 62), sb = b % ((i128)1 << 62);
    u64 xs = mk_int(sa), ys = mk_int(sb);
    r = lcnf_int_op(rt, 6, xs, ys); CHECK("mul", rd_int(r), sa * sb); dec(r);
    dec(xs); dec(ys);
    i128 q, m, tq, tm;
    if (b == 0) { q = 0; m = a; tq = 0; tm = a; }
    else {
      tq = a / b; tm = a % b;
      q = tq; m = tm;
      if (m < 0) { if (b > 0) { q -= 1; m += b; } else { q += 1; m -= b; } }
    }
    r = lcnf_int_op(rt, 7, x, y); CHECK("ediv", rd_int(r), q); dec(r);
    r = lcnf_int_op(rt, 8, x, y); CHECK("emod", rd_int(r), m); dec(r);
    r = lcnf_int_op(rt, 14, x, y); CHECK("tdiv", rd_int(r), tq); dec(r);
    r = lcnf_int_op(rt, 15, x, y); CHECK("tmod", rd_int(r), tm); dec(r);
    r = lcnf_int_op(rt, 3, x, 1); CHECK("neg", rd_int(r), -a); dec(r);
    CHECK("decEq", (i128)lcnf_int_op(rt, 10, x, y), a == b);
    CHECK("decLt", (i128)lcnf_int_op(rt, 11, x, y), a < b);
    CHECK("decLe", (i128)lcnf_int_op(rt, 12, x, y), a <= b);
    CHECK("decNonneg", (i128)lcnf_int_op(rt, 16, x, 1), a >= 0);
    int64_t s = (int64_t)rnd64();
    if (it % 5 == 0) s = INT64_MIN + it % 3;
    r = lcnf_int_op(rt, 13, (u64)s, 1); CHECK("ofInt64", rd_int(r), (i128)s); dec(r);
    if (a >= 0) {
      u64 n = nat_of_u128((u128x)a);
      r = lcnf_int_op(rt, 2, n, 1); CHECK("negSucc", rd_int(r), -a - 1); dec(r);
    }
    dec(x); dec(y);
  }
  LcnfStats *st = &lcnf_state(rt)->st;
  fprintf(stderr, "INTFUZZ allocs=%llu live=%llu persistent=%llu fails=%d\n",
          (unsigned long long)st->allocs, (unsigned long long)st->live,
          (unsigned long long)st->persistent, fails);
  if (st->live != st->persistent) { fprintf(stderr, "LEAK\n"); return 1; }
  if (!fails) fprintf(stderr, "LEAKCHECK ok (lcnf_int_op fuzz)\n");
  lcnf_rt_free(rt);
  return fails ? 1 : 0;
}
