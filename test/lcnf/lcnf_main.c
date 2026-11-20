/* lcnf_main.c: differential test + benchmark driver for the LCNF -> LeanQbe.T demo programs.
 *
 *   lcnf_main            print the differential results (stdout, compared bit-for-bit with the
 *                        native Lean 4 oracle), telemetry to stderr, and enforce the
 *                        `live == persistent` zero-leak check after every call and the FBIP
 *                        in-place reuse assertion.
 *   lcnf_main bench      time the benchmark workloads (stdout: `BENCH <name> <ms> <result>`).
 *
 * Native builds link LeanQbe.T assembly (x86-64 / Arm64).  With -DLCNF_TQBE this file is compiled
 * as C++ together with the PrintCpp translation unit (`lcnf_gen.hpp`): every object then lives in
 * the simulated `tqbe::Mem` and the runtime entry points are wrapped below.
 */
#ifdef LCNF_TQBE
#include "tqbe_rt.hpp"
#include "lcnf_rt.h"
#include "lcnf_gen.hpp"
#include "lcnf_rt.c"
#else
#include "lcnf_rt.h"
#endif
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define DEMO(n) l_LeanQbe_T_LeanLCNF_Demo_##n
#define l_LeanQbe_T_LeanLCNF_Demo_Probe_resetDec l_LeanQbe_T_LeanLCNF_Probe_resetDec
#define l_LeanQbe_T_LeanLCNF_Demo_Probe_reuse l_LeanQbe_T_LeanLCNF_Probe_reuse

#ifdef LCNF_TQBE
typedef ::tqbe::bits<64> W;
static ::tqbe::Mem g_mem;
#define RT_ADDR 0x10000ULL
static u64 g_rt = RT_ADDR;
static W w(u64 x) { return W(x); }
/* Runtime entry points with the PrintCpp calling convention. */
W lcnf_alloc(::tqbe::Mem &, W rt, W sz) { return w(rt_lcnf_alloc(rt.word(0), sz.word(0))); }
std::tuple<> lcnf_dec_ref_cold(::tqbe::Mem &, W rt, W o) {
  rt_lcnf_dec_ref_cold(rt.word(0), o.word(0));
  return {};
}
std::tuple<> lcnf_free_obj(::tqbe::Mem &, W rt, W o) {
  rt_lcnf_free_obj(rt.word(0), o.word(0));
  return {};
}
std::tuple<> lcnf_mark_persistent(::tqbe::Mem &, W rt, W o) {
  rt_lcnf_mark_persistent(rt.word(0), o.word(0));
  return {};
}
W lcnf_nat_slow(::tqbe::Mem &, W rt, W op, W a, W b) {
  return w(rt_lcnf_nat_slow(rt.word(0), op.word(0), a.word(0), b.word(0)));
}
W lcnf_clo_under(::tqbe::Mem &, W rt, W f, W k) {
  return w(rt_lcnf_clo_under(rt.word(0), f.word(0), k.word(0)));
}
#define CALL1(f, a) DEMO(f)(g_mem, w(g_rt), w(a)).word(0)
#define CALL2(f, a, b) DEMO(f)(g_mem, w(g_rt), w(a), w(b)).word(0)
#define CALL3(f, a, b, c) DEMO(f)(g_mem, w(g_rt), w(a), w(b), w(c)).word(0)
#define CALL4(f, a, b, c, d) DEMO(f)(g_mem, w(g_rt), w(a), w(b), w(c), w(d)).word(0)
static void rt_setup(void) {
  lcnf_tqbe_mem = &g_mem;
  g_mem.alloc(RT_ADDR, LCNF_RT_T_BYTES, 0);
  lcnf_rt_init(g_rt);
}
#else
u64 DEMO(rbBench)(u64 rt, u64 n);
u64 DEMO(rbPersist)(u64 rt, u64 n);
u64 DEMO(rbLinear)(u64 rt, u64 n, u64 reps);
u64 DEMO(rbShared)(u64 rt, u64 n, u64 reps);
u64 DEMO(sortBench)(u64 rt, u64 n, u64 seed);
u64 DEMO(satSolve)(u64 rt, u64 kind, u64 a, u64 b, u64 seed);
u64 DEMO(vmBench)(u64 rt, u64 n, u64 depth, u64 seed);
u64 DEMO(usizeSum)(u64 rt, u64 n);
u64 l_LeanQbe_T_LeanLCNF_Probe_resetDec(u64 rt, u64 n);
u64 l_LeanQbe_T_LeanLCNF_Probe_reuse(u64 rt, u64 n);
static LcnfRt g_rtblock;
static u64 g_rt;
#define CALL1(f, a) DEMO(f)(g_rt, a)
#define CALL2(f, a, b) DEMO(f)(g_rt, a, b)
#define CALL3(f, a, b, c) DEMO(f)(g_rt, a, b, c)
#define CALL4(f, a, b, c, d) DEMO(f)(g_rt, a, b, c, d)
static void rt_setup(void) {
  g_rt = (u64)(uintptr_t)&g_rtblock;
  lcnf_rt_init(g_rt);
}
#endif

static u64 bx(u64 n) { return (n << 1) | 1ULL; }

/* Unbox a Lean `Nat` result (all demo results are small). */
static u64 ub(const char *what, u64 x) {
  if ((x & 1ULL) == 0) {
    fprintf(stderr, "FAIL %s: result %#llx is not a tagged scalar\n", what, (unsigned long long)x);
    exit(1);
  }
  return x >> 1;
}

static int g_fail = 0;

/* Zero-leak check: everything allocated by a call is freed, except persistent constants. */
static void leak_check(const char *what) {
  LcnfStats *st = &lcnf_state(g_rt)->st;
  if (st->live != st->persistent) {
    fprintf(stderr, "FAIL leak after %s: live=%llu persistent=%llu\n", what,
            (unsigned long long)st->live, (unsigned long long)st->persistent);
    g_fail = 1;
  }
}

static u64 allocs(void) { return lcnf_state(g_rt)->st.allocs; }

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1e3 + (double)ts.tv_nsec / 1e6;
}

/* Differential workloads (sizes may be scaled down for the slow PrintCpp memory model). */
static void run_tests(int quick) {
  static const u64 rbN[] = {0, 1, 2, 3, 7, 10, 64, 100, 500, 1000, 2000};
  for (size_t i = 0; i < sizeof rbN / sizeof rbN[0]; i++) {
    u64 n = rbN[i];
    if (quick && n > 200) continue;
    u64 a = ub("rbBench", CALL1(rbBench, bx(n)));
    leak_check("rbBench");
    u64 b = ub("rbPersist", CALL1(rbPersist, bx(n)));
    leak_check("rbPersist");
    u64 c = ub("rbLinear", CALL2(rbLinear, bx(n), bx(3)));
    leak_check("rbLinear");
    u64 d = ub("rbShared", CALL2(rbShared, bx(n), bx(3)));
    leak_check("rbShared");
    printf("RB n=%llu bench=%llu persist=%llu linear=%llu shared=%llu\n", (unsigned long long)n,
           (unsigned long long)a, (unsigned long long)b, (unsigned long long)c,
           (unsigned long long)d);
  }
  /* FBIP: extra mapValues passes over a linear tree allocate nothing; over shared versions they
   * copy every node once per pass. */
  {
    u64 n = quick ? 200 : 2000, reps = 10;
    u64 a0 = allocs(); (void)CALL2(rbLinear, bx(n), bx(0)); u64 a1 = allocs();
    (void)CALL2(rbLinear, bx(n), bx(reps)); u64 a2 = allocs();
    (void)CALL2(rbShared, bx(n), bx(0)); u64 a3 = allocs();
    (void)CALL2(rbShared, bx(n), bx(reps)); u64 a4 = allocs();
    leak_check("fbip");
    long long lin = (long long)(a2 - a1) - (long long)(a1 - a0);
    long long sh = (long long)(a4 - a3) - (long long)(a3 - a2);
    fprintf(stderr, "FBIP n=%llu reps=%llu linear_extra_allocs=%lld shared_extra_allocs=%lld\n",
            (unsigned long long)n, (unsigned long long)reps, lin, sh);
    if (lin != 0 || sh != (long long)(n * reps)) {
      fprintf(stderr, "FAIL fbip: expected 0 / %llu extra allocations\n",
              (unsigned long long)(n * reps));
      g_fail = 1;
    }
  }
  static const u64 sortN[][2] = {{0, 1}, {1, 2}, {2, 3}, {3, 9}, {10, 4}, {100, 5}, {500, 6},
                                 {1000, 7}, {2000, 8}};
  for (size_t i = 0; i < sizeof sortN / sizeof sortN[0]; i++) {
    if (quick && sortN[i][0] > 200) continue;
    u64 r = ub("sortBench", CALL2(sortBench, bx(sortN[i][0]), bx(sortN[i][1])));
    leak_check("sortBench");
    printf("SORT n=%llu seed=%llu r=%llu\n", (unsigned long long)sortN[i][0],
           (unsigned long long)sortN[i][1], (unsigned long long)r);
  }
  static const u64 sat[][4] = {{0, 2, 1, 0}, {0, 3, 2, 0}, {0, 3, 3, 0}, {0, 4, 3, 0},
                               {0, 4, 4, 0}, {0, 5, 4, 0}, {1, 10, 30, 1}, {1, 10, 50, 2},
                               {1, 12, 70, 9}, {1, 15, 60, 3}, {1, 16, 90, 10}, {1, 20, 80, 4},
                               {1, 20, 91, 5}, {1, 25, 100, 6}, {1, 30, 120, 7},
                               {1, 30, 150, 8}};
  for (size_t i = 0; i < sizeof sat / sizeof sat[0]; i++) {
    if (quick && sat[i][0] == 0 && sat[i][1] > 4) continue;
    u64 r = ub("satSolve", CALL4(satSolve, bx(sat[i][0]), bx(sat[i][1]), bx(sat[i][2]),
                                 bx(sat[i][3])));
    leak_check("satSolve");
    printf("SAT kind=%llu a=%llu b=%llu seed=%llu sat=%llu nodes=%llu\n",
           (unsigned long long)sat[i][0], (unsigned long long)sat[i][1],
           (unsigned long long)sat[i][2], (unsigned long long)sat[i][3],
           (unsigned long long)(r & 1), (unsigned long long)(r >> 1));
  }
  static const u64 vm[][3] = {{0, 0, 1}, {1, 1, 1}, {10, 3, 2}, {100, 5, 3}, {1000, 8, 4},
                              {3000, 10, 5}};
  for (size_t i = 0; i < sizeof vm / sizeof vm[0]; i++) {
    if (quick && vm[i][0] > 100) continue;
    u64 r = CALL3(vmBench, bx(vm[i][0]), bx(vm[i][1]), bx(vm[i][2]));
    leak_check("vmBench");
    printf("VM n=%llu depth=%llu seed=%llu r=%llu\n", (unsigned long long)vm[i][0],
           (unsigned long long)vm[i][1], (unsigned long long)vm[i][2], (unsigned long long)r);
  }
  static const u64 usz[] = {0, 1, 10, 100, 1000};
  for (size_t i = 0; i < sizeof usz / sizeof usz[0]; i++) {
    u64 r = ub("usizeSum", CALL1(usizeSum, bx(usz[i])));
    leak_check("usizeSum");
    printf("USZ n=%llu r=%llu\n", (unsigned long long)usz[i], (unsigned long long)r);
  }
  /* Hand-built LCNF probes: `reset` token `dec`'d without reuse, and `reset`/`reuse` + setTag. */
  {
    u64 a0 = allocs();
    u64 p1 = ub("Probe.resetDec", CALL1(Probe_resetDec, bx(5)));
    leak_check("Probe.resetDec");
    u64 p2 = ub("Probe.reuse", CALL1(Probe_reuse, bx(9)));
    leak_check("Probe.reuse");
    u64 da = allocs() - a0;
    fprintf(stderr, "PROBE resetDec=%llu reuse=%llu allocs=%llu\n", (unsigned long long)p1,
            (unsigned long long)p2, (unsigned long long)da);
    if (p1 != 5 || p2 != 9 || da != 3) {
      fprintf(stderr, "FAIL probes: expected resetDec=5 reuse=9 allocs=3\n");
      g_fail = 1;
    }
  }
}

#define BENCH(name, expr)                                                          \
  do {                                                                             \
    LcnfStats s0 = lcnf_state(g_rt)->st;                                           \
    double t0 = now_ms();                                                          \
    u64 r_ = (expr);                                                               \
    double t1 = now_ms();                                                          \
    LcnfStats s1 = lcnf_state(g_rt)->st;                                           \
    leak_check(name);                                                              \
    printf("BENCH %s %.1f %llu\n", name, t1 - t0, (unsigned long long)r_);         \
    fprintf(stderr, "STAT %s allocs=%llu reused=%llu peak=%llu cold_decs=%llu\n", name, \
            (unsigned long long)(s1.allocs - s0.allocs),                            \
            (unsigned long long)(s1.reused - s0.reused), (unsigned long long)s1.peak_live, \
            (unsigned long long)(s1.cold_decs - s0.cold_decs));                     \
  } while (0)

static void run_bench(void) {
  BENCH("rbmap", ub("rbmap", CALL1(rbBench, bx(200000))));
  BENCH("rbmap_fbip", ub("rbmap_fbip", CALL2(rbLinear, bx(100000), bx(20))));
  BENCH("mergesort", ub("mergesort", CALL2(sortBench, bx(50000), bx(42))));
  BENCH("dpll_php87", ub("dpll_php87", CALL4(satSolve, bx(0), bx(8), bx(7), bx(0))));
  BENCH("dpll_rand", ub("dpll_rand", CALL4(satSolve, bx(1), bx(70), bx(298), bx(11))));
  BENCH("exprvm", CALL3(vmBench, bx(30000), bx(10), bx(77)));
}

int main(int argc, char **argv) {
  rt_setup();
  int quick = argc > 1 && strcmp(argv[1], "quick") == 0;
  if (argc > 1 && strcmp(argv[1], "bench") == 0) run_bench();
  else run_tests(quick);
  lcnf_rt_print_stats(g_rt, "total", stderr);
  leak_check("total");
  lcnf_rt_free(g_rt);
  if (g_fail) return 1;
  fprintf(stderr, "LEAKCHECK ok (live == persistent after every call)\n");
  return 0;
}
