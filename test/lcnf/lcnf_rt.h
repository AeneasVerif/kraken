/* lcnf_rt.h: Tier-0 C runtime for Lean 4 impure LCNF lowered to LeanQbe.T.
 *
 * Shared by the native x86-64 / Arm64 builds (real pointers) and by the PrintCpp build
 * (`-DLCNF_TQBE`, objects live in the simulated `tqbe::Mem`).  The T code only touches
 * `extra_args` (@0) and `globals` (@256) of the runtime block and the object heap; all other
 * state (allocator, telemetry) is C-only.
 */
#ifndef LCNF_RT_H
#define LCNF_RT_H

#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef uint64_t u64;

#define LCNF_EXTRA_SLOTS 32
#define LCNF_GLOBAL_SLOTS 256
#define LCNF_RT_T_BYTES (8 * (LCNF_EXTRA_SLOTS + LCNF_GLOBAL_SLOTS))
#define LCNF_NUM_CLASSES 64 /* size classes of 8..504 bytes (index = bytes / 8) */
#define LCNF_CLOSURE_TAG 245

typedef struct {
  u64 allocs;      /* objects handed out by lcnf_alloc */
  u64 frees;       /* objects returned (lcnf_free_obj / lcnf_dec_ref_cold) */
  u64 live;        /* allocs - frees */
  u64 peak_live;   /* maximum of live */
  u64 persistent;  /* objects marked persistent (closed constants), never freed */
  u64 reused;      /* allocations served from a size-class free list */
  u64 cold_decs;   /* calls of lcnf_dec_ref_cold (m_rc dropped 1 -> 0) */
  u64 bytes;       /* total bytes allocated */
} LcnfStats;

typedef struct {
  u64 free_list[LCNF_NUM_CLASSES];
  u64 cur, end;          /* bump region */
  u64 *work;             /* worklist of lcnf_dec_ref_cold / lcnf_mark_persistent */
  u64 work_cap;
  void **chunks;         /* native heap chunks (freed by lcnf_rt_free) */
  u64 nchunks, chunks_cap;
  LcnfStats st;
} LcnfState;

/* The runtime block passed as `rt` (native builds). */
typedef struct {
  u64 extra_args[LCNF_EXTRA_SLOTS]; /* @0   : parameters 5.. of calls */
  u64 globals[LCNF_GLOBAL_SLOTS];   /* @256 : once-cells of closed constants */
  LcnfState s;                      /* C-only */
} LcnfRt;

/* Entry points called from LeanQbe.T code (all arguments / results are 64-bit). */
u64 lcnf_alloc(u64 rt, u64 sz);
void lcnf_dec_ref_cold(u64 rt, u64 o);
void lcnf_free_obj(u64 rt, u64 o);
void lcnf_mark_persistent(u64 rt, u64 o);
u64 lcnf_nat_slow(u64 rt, u64 op, u64 a, u64 b);
u64 lcnf_clo_under(u64 rt, u64 f, u64 k);
#ifndef LCNF_TQBE
void lcnf_panic(u64 rt, u64 code) __attribute__((noreturn));
#endif

/* Driver API. */
LcnfState *lcnf_state(u64 rt);
void lcnf_rt_init(u64 rt);
void lcnf_rt_free(u64 rt);
void lcnf_rt_print_stats(u64 rt, const char *tag, FILE *f);

#ifdef __cplusplus
}
#endif

#endif
