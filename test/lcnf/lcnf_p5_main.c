/* lcnf_p5_main.c: differential test driver for LeanQbe.T.LeanLCNF.Coverage (P5). */
#ifdef LCNF_TQBE
#include "tqbe_rt.hpp"
#include "lcnf_rt.h"
#include "lcnf_p5_gen.hpp"
#include "lcnf_rt.c"
#include "lcnf_tqbe_wrappers.h"
#else
#include "lcnf_rt.h"
#endif
#include <stdlib.h>
#include <string.h>

#define COV(n) l_LeanQbe_T_LeanLCNF_Coverage_##n

#ifdef LCNF_TQBE
#define CALL1(f, a) COV(f)(g_mem, w(g_rt), w(a)).word(0)
#define CALL2(f, a, b) COV(f)(g_mem, w(g_rt), w(a), w(b)).word(0)
#else
u64 COV(strLitTest)(u64 rt, u64 n);
u64 COV(strBuildBench)(u64 rt, u64 n);
u64 COV(bigNatBench)(u64 rt, u64 n);
u64 COV(arrBench)(u64 rt, u64 n);
u64 COV(arrLinear)(u64 rt, u64 n, u64 reps);
u64 COV(arrShared)(u64 rt, u64 n, u64 reps);
u64 COV(byteArrBench)(u64 rt, u64 n);
u64 COV(floatBench)(u64 rt, u64 n);
u64 COV(intBench)(u64 rt, u64 n);
u64 COV(bitVecIntBench)(u64 rt, u64 n);
u64 COV(int64Bench)(u64 rt, u64 n);
u64 COV(uintBvBench)(u64 rt, u64 n);
u64 COV(shapeBench)(u64 rt, u64 n);
u64 COV(usizeBench)(u64 rt, u64 n);
u64 COV(shaMix)(u64 rt, u64 n);
static LcnfRt g_rtblock;
static u64 g_rt;
#define CALL1(f, a) COV(f)(g_rt, a)
#define CALL2(f, a, b) COV(f)(g_rt, a, b)
static void rt_setup(void) {
  g_rt = (u64)(uintptr_t)&g_rtblock;
  lcnf_rt_init(g_rt);
}
#endif

static u64 bx(u64 n) { return (n << 1) | 1ULL; }

static u64 ub(const char *what, u64 x) {
  if ((x & 1ULL) == 0) {
    fprintf(stderr, "FAIL %s: result %#llx is not a tagged scalar\n", what, (unsigned long long)x);
    exit(1);
  }
  return x >> 1;
}

static int g_fail = 0;

static void leak_check(const char *what) {
  LcnfStats *st = &lcnf_state(g_rt)->st;
  if (st->live != st->persistent) {
    fprintf(stderr, "FAIL leak after %s: live=%llu persistent=%llu\n", what,
            (unsigned long long)st->live, (unsigned long long)st->persistent);
    g_fail = 1;
  }
}

static u64 allocs(void) { return lcnf_state(g_rt)->st.allocs; }

int main(int argc, char **argv) {
  rt_setup();
  int quick = argc > 1 && strcmp(argv[1], "quick") == 0;

  static const u64 strN[] = {0, 1, 7, 42, 123456789};
  for (size_t i = 0; i < sizeof strN / sizeof strN[0]; i++) {
    u64 r = ub("strLitTest", CALL1(strLitTest, bx(strN[i])));
    leak_check("strLitTest");
    printf("STR n=%llu lit=%llu\n", (unsigned long long)strN[i], (unsigned long long)r);
  }

  static const u64 sbldN[] = {0, 1, 15, 64, 600};
  for (size_t i = 0; i < sizeof sbldN / sizeof sbldN[0]; i++) {
    if (quick && sbldN[i] > 100) continue;
    u64 r = ub("strBuildBench", CALL1(strBuildBench, bx(sbldN[i])));
    leak_check("strBuildBench");
    printf("SBLD n=%llu r=%llu\n", (unsigned long long)sbldN[i], (unsigned long long)r);
  }

  static const u64 bnatN[] = {0, 1, 5, 19};
  for (size_t i = 0; i < sizeof bnatN / sizeof bnatN[0]; i++) {
    u64 r = ub("bigNatBench", CALL1(bigNatBench, bx(bnatN[i])));
    leak_check("bigNatBench");
    printf("BNAT n=%llu r=%llu\n", (unsigned long long)bnatN[i], (unsigned long long)r);
  }

  static const u64 arrN[] = {2, 10, 80, 150};
  for (size_t i = 0; i < sizeof arrN / sizeof arrN[0]; i++) {
    if (quick && arrN[i] > 80) continue;
    u64 a = ub("arrBench", CALL1(arrBench, bx(arrN[i])));
    leak_check("arrBench");
    u64 l = ub("arrLinear", CALL2(arrLinear, bx(arrN[i]), bx(20)));
    leak_check("arrLinear");
    u64 s = ub("arrShared", CALL2(arrShared, bx(arrN[i]), bx(10)));
    leak_check("arrShared");
    printf("ARR n=%llu bench=%llu lin=%llu sh=%llu\n", (unsigned long long)arrN[i],
           (unsigned long long)a, (unsigned long long)l, (unsigned long long)s);
  }

  /* Array FBIP in-place mutation check: extra set! reps on linear array allocate 0 cells. */
  {
    u64 n = quick ? 40 : 120, reps = 30;
    u64 a0 = allocs(); (void)CALL2(arrLinear, bx(n), bx(0)); u64 a1 = allocs();
    (void)CALL2(arrLinear, bx(n), bx(reps)); u64 a2 = allocs();
    (void)CALL2(arrShared, bx(n), bx(0)); u64 a3 = allocs();
    (void)CALL2(arrShared, bx(n), bx(reps)); u64 a4 = allocs();
    leak_check("fbip_arr");
    long long lin = (long long)(a2 - a1) - (long long)(a1 - a0);
    long long sh = (long long)(a4 - a3) - (long long)(a3 - a2);
    fprintf(stderr, "FBIP_ARR n=%llu reps=%llu linear_extra=%lld shared_extra=%lld\n",
            (unsigned long long)n, (unsigned long long)reps, lin, sh);
    if (lin != 0 || sh <= 0) {
      fprintf(stderr, "FAIL fbip_arr: expected linear_extra==0 and shared_extra>0\n");
      g_fail = 1;
    }
  }

  static const u64 baN[] = {1, 10, 100, 600};
  for (size_t i = 0; i < sizeof baN / sizeof baN[0]; i++) {
    if (quick && baN[i] > 100) continue;
    u64 r = ub("byteArrBench", CALL1(byteArrBench, bx(baN[i])));
    leak_check("byteArrBench");
    printf("BA n=%llu r=%llu\n", (unsigned long long)baN[i], (unsigned long long)r);
  }

  static const u64 fltN[] = {0, 1, 7, 42};
  for (size_t i = 0; i < sizeof fltN / sizeof fltN[0]; i++) {
    u64 r = CALL1(floatBench, bx(fltN[i]));
    leak_check("floatBench");
    printf("FLT n=%llu r=%llu\n", (unsigned long long)fltN[i], (unsigned long long)r);
  }

  /* Int (small + bignum, all sign combinations), BitVec.toInt/ofInt, Int64, UIntN.ofBitVec,
   * getObjTagNat (derived DecidableEq / ctorIdx), USize.{ofNatLT,repr}, non-ASCII symbols. */
  static const u64 intN[] = {0, 1, 5, 977};
  for (size_t i = 0; i < sizeof intN / sizeof intN[0]; i++) {
    if (quick && intN[i] > 5) continue;
    u64 r = ub("intBench", CALL1(intBench, bx(intN[i])));
    leak_check("intBench");
    printf("INT n=%llu r=%llu\n", (unsigned long long)intN[i], (unsigned long long)r);
  }
  static const u64 bviN[] = {0, 1, 7, 42, 89, 1000};
  for (size_t i = 0; i < sizeof bviN / sizeof bviN[0]; i++) {
    u64 r = ub("bitVecIntBench", CALL1(bitVecIntBench, bx(bviN[i])));
    leak_check("bitVecIntBench");
    printf("BVI n=%llu r=%llu\n", (unsigned long long)bviN[i], (unsigned long long)r);
  }
  static const u64 i64N[] = {0, 1, 7, 123456789};
  for (size_t i = 0; i < sizeof i64N / sizeof i64N[0]; i++) {
    u64 a = ub("int64Bench", CALL1(int64Bench, bx(i64N[i])));
    leak_check("int64Bench");
    u64 b = ub("uintBvBench", CALL1(uintBvBench, bx(i64N[i])));
    leak_check("uintBvBench");
    u64 c = ub("shapeBench", CALL1(shapeBench, bx(i64N[i] % 100)));
    leak_check("shapeBench");
    printf("I64 n=%llu r=%llu ubv=%llu sh=%llu\n", (unsigned long long)i64N[i],
           (unsigned long long)a, (unsigned long long)b, (unsigned long long)c);
  }
  static const u64 miscN[] = {0, 9, 4294967296ULL};
  for (size_t i = 0; i < sizeof miscN / sizeof miscN[0]; i++) {
    u64 a = ub("usizeBench", CALL1(usizeBench, bx(miscN[i])));
    leak_check("usizeBench");
    u64 b = ub("shaMix", CALL1(shaMix, bx(miscN[i])));
    leak_check("shaMix");
    printf("MISC n=%llu us=%llu sha=%llu\n", (unsigned long long)miscN[i], (unsigned long long)a,
           (unsigned long long)b);
  }

  lcnf_rt_print_stats(g_rt, "total", stderr);
  leak_check("total");
  lcnf_rt_free(g_rt);
  if (g_fail) return 1;
  fprintf(stderr, "LEAKCHECK ok (live == persistent after every call)\n");
  return 0;
}
