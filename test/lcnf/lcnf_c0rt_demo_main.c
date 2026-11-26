/* Differential driver for `LeanQbe.T.LeanLCNF.DemoNatStr` (`addNat`, `addToStr`,
 * `fmtSumTagged`) plus `lcnf_panic` exit-code verification.
 *
 * Linked against BOTH `lcnf_rt.c` (reference) and the verified compiled C0 runtime
 * (`rtC0CoreMod` `.o` + `lcnf_c0rt_shim.c` under `-DLCNF_C0RT`).
 */
#include "lcnf_rt.h"
#include <stdlib.h>
#include <string.h>

#define NATSTR(n) l_LeanQbe_T_LeanLCNF_DemoNatStr_##n

u64 NATSTR(addNat)(u64 rt, u64 a, u64 b);
u64 NATSTR(addToStr)(u64 rt, u64 a, u64 b);
u64 NATSTR(fmtSumTagged)(u64 rt, u64 tag, u64 a, u64 b);

static LcnfC0RtBlock g_rtblock;
static u64 g_rt;
static int g_fail = 0;

static u64 bx(u64 n) { return (n << 1) | 1ULL; }

static void dec_obj(u64 o) {
  if ((o & 1ULL) != 0ULL) return;
  uint32_t rc = 0;
  memcpy(&rc, (const void *)(uintptr_t)o, 4);
  if (rc == 1U) lcnf_dec_ref_cold(g_rt, o);
  else if (rc > 1U) {
    rc -= 1U;
    memcpy((void *)(uintptr_t)o, &rc, 4);
  }
}

static void leak_check(const char *what) {
  LcnfStats *st = &lcnf_state(g_rt)->st;
  if (st->live != st->persistent) {
    fprintf(stderr, "FAIL leak after %s: live=%llu persistent=%llu\n", what,
            (unsigned long long)st->live, (unsigned long long)st->persistent);
    g_fail = 1;
  }
}

static u64 mk_cstr(const char *s) {
  size_t len = strlen(s);
  u64 obj = lcnf_str_alloc(g_rt, (u64)len, (u64)len);
  if (len > 0) memcpy((void *)(uintptr_t)(obj + 32ULL), s, len);
  return obj;
}

static const char *rd_cstr(u64 obj) {
  return (const char *)(uintptr_t)(obj + 32ULL);
}

static u64 mk_mpz2(u64 lo, u64 hi) {
  u64 p = lcnf_nat_alloc(g_rt, 2);
  memcpy((void *)(uintptr_t)(p + 16ULL), &lo, 8);
  memcpy((void *)(uintptr_t)(p + 24ULL), &hi, 8);
  return p;
}

int main(int argc, char **argv) {
  g_rt = (u64)(uintptr_t)&g_rtblock;
  lcnf_rt_init(g_rt);

  if (argc > 1 && strcmp(argv[1], "--panic") == 0) {
    /* Trigger `lcnf_panic` via invalid `lcnf_nat_slow` op code -> must exit 4. */
    (void)lcnf_nat_slow(g_rt, 99, bx(1), bx(1));
    fprintf(stderr, "FAIL: lcnf_nat_slow invalid op did not panic\n");
    return 1;
  }

  /* 1. Small scalar `addNat` & `addToStr` */
  {
    u64 r0 = NATSTR(addNat)(g_rt, bx(0), bx(0));
    u64 r1 = NATSTR(addNat)(g_rt, bx(17), bx(25));
    u64 s0 = NATSTR(addToStr)(g_rt, bx(0), bx(0));
    u64 s1 = NATSTR(addToStr)(g_rt, bx(17), bx(25));
    printf("ADD_SMALL %llu %llu STR %s %s\n", (unsigned long long)(r0 >> 1),
           (unsigned long long)(r1 >> 1), rd_cstr(s0), rd_cstr(s1));
    dec_obj(r0);
    dec_obj(r1);
    dec_obj(s0);
    dec_obj(s1);
    leak_check("small");
  }

  /* 2. Carry-overflow & multi-limb MPZ `addNat` + `addToStr` */
  {
    u64 big_ovf = NATSTR(addNat)(g_rt, bx((1ULL << 62)), bx((1ULL << 62)));
    u64 s_ovf = lcnf_nat_to_str(g_rt, big_ovf);
    u64 a = mk_mpz2(0xffffffffffffffffULL, 1ULL);
    u64 b = mk_mpz2(5ULL, 2ULL);
    u64 sum = NATSTR(addNat)(g_rt, a, b);
    u64 s_sum = NATSTR(addToStr)(g_rt, a, b);
    u64 s_sum2 = lcnf_nat_to_str(g_rt, sum);
    printf("ADD_MPZ %s %s %s\n", rd_cstr(s_ovf), rd_cstr(s_sum), rd_cstr(s_sum2));
    dec_obj(a);
    dec_obj(b);
    dec_obj(s_ovf);
    dec_obj(s_sum);
    dec_obj(s_sum2);
    leak_check("mpz");
  }

  /* 3. `fmtSumTagged` (in-place / COW `lcnf_string_append` + `lcnf_dec_ref_cold`) */
  {
    u64 t1 = mk_cstr("sum=");
    u64 out1 = NATSTR(fmtSumTagged)(g_rt, t1, bx(17), bx(25));
    u64 a = mk_mpz2(0xffffffffffffffffULL, 1ULL);
    u64 b = mk_mpz2(5ULL, 2ULL);
    u64 t2 = mk_cstr("big=");
    u64 out2 = NATSTR(fmtSumTagged)(g_rt, t2, a, b);
    printf("FMT %s | %s\n", rd_cstr(out1), rd_cstr(out2));
    dec_obj(out1);
    dec_obj(out2);
    dec_obj(a);
    dec_obj(b);
    leak_check("fmtSumTagged");
  }

  lcnf_rt_print_stats(g_rt, "c0demo", stderr);
  leak_check("total");
  lcnf_rt_free(g_rt);
  if (g_fail) return 1;
  fprintf(stderr, "LEAKCHECK ok (LcnfC0Demo)\n");
  return 0;
}
