/* Minimal host slab-init & panic shim for linking float-free LCNF programs against
 * the verified compiled C0 runtime (`rtC0CoreMod` compiled by leanqbe / leanqbe-arm64).
 *
 * Intentionally defines ONLY the 5 host/driver symbols (`lcnf_panic`, `lcnf_rt_init`,
 * `lcnf_rt_free`, `lcnf_state`, `lcnf_rt_print_stats`) and ZERO `lcnf_rt.c` runtime
 * entry points (`lcnf_alloc`, `lcnf_dec_ref_cold`, `lcnf_nat_*`, `lcnf_int_op`,
 * `lcnf_array_*`, `lcnf_ba_*`, `lcnf_string_*`, etc.).
 */
#ifndef LCNF_C0RT
#define LCNF_C0RT 1
#endif
#include "lcnf_rt.h"
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#define C0RT_SLAB_BYTES  (64ULL << 20) /* 64 MiB contiguous bump slab */
#define C0RT_WORK_CAP    262144ULL     /* 262144 u64 DFS worklist slots */
#define C0RT_SCRATCH_CAP 4096ULL       /* 4096 u64 BigNum scratch limbs */

static void shim_fatal(const char *msg) {
  fprintf(stderr, "lcnf_c0rt_shim: fatal: %s\n", msg);
  exit(3);
}

LcnfState *lcnf_state(u64 rt) {
  return &((LcnfC0RtBlock *)(uintptr_t)rt)->base.s;
}

void lcnf_panic(u64 rt, u64 code) {
  (void)rt;
  fprintf(stderr, "lcnf_rt: panic %llu\n", (unsigned long long)code);
  exit(4);
}

void lcnf_rt_init(u64 rt) {
  (void)sizeof(char[sizeof(LcnfC0RtBlock) == 33688 ? 1 : -1]);
  (void)sizeof(char[offsetof(LcnfC0RtBlock, scratch) == 33672 ? 1 : -1]);
  (void)sizeof(char[offsetof(LcnfC0RtBlock, scratch_cap) == 33680 ? 1 : -1]);
  LcnfC0RtBlock *blk = (LcnfC0RtBlock *)(uintptr_t)rt;
  memset(blk, 0, sizeof(*blk));
  void *slab = calloc(1, (size_t)C0RT_SLAB_BYTES);
  u64 *work = (u64 *)calloc((size_t)C0RT_WORK_CAP, sizeof(u64));
  u64 *scr = (u64 *)calloc((size_t)C0RT_SCRATCH_CAP, sizeof(u64));
  if (!slab || !work || !scr) shim_fatal("out of memory");
  blk->base.s.chunks = (void **)slab;
  blk->base.s.nchunks = 1;
  blk->base.s.cur = (u64)(uintptr_t)slab;
  blk->base.s.end = blk->base.s.cur + C0RT_SLAB_BYTES;
  blk->base.s.work = work;
  blk->base.s.work_cap = C0RT_WORK_CAP;
  blk->scratch = (u64)(uintptr_t)scr;
  blk->scratch_cap = C0RT_SCRATCH_CAP;
}

void lcnf_rt_free(u64 rt) {
  LcnfC0RtBlock *blk = (LcnfC0RtBlock *)(uintptr_t)rt;
  free((void *)blk->base.s.chunks);
  free(blk->base.s.work);
  free((void *)(uintptr_t)blk->scratch);
  memset(blk, 0, sizeof(*blk));
}

void lcnf_rt_print_stats(u64 rt, const char *tag, FILE *f) {
  LcnfStats *st = &lcnf_state(rt)->st;
  fprintf(f,
          "STAT %s allocs=%llu frees=%llu live=%llu peak=%llu persistent=%llu reused=%llu "
          "cold_decs=%llu bytes=%llu\n",
          tag, (unsigned long long)st->allocs, (unsigned long long)st->frees,
          (unsigned long long)st->live, (unsigned long long)st->peak_live,
          (unsigned long long)st->persistent, (unsigned long long)st->reused,
          (unsigned long long)st->cold_decs, (unsigned long long)st->bytes);
}
