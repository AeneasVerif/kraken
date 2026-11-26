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
#define LCNF_GLOBAL_SLOTS 4096
#define LCNF_RT_T_BYTES (8 * (LCNF_EXTRA_SLOTS + LCNF_GLOBAL_SLOTS))
#define LCNF_NUM_CLASSES 64 /* size classes of 8..504 bytes (index = bytes / 8) */
#define LCNF_CLOSURE_TAG 245
#define LCNF_ARRAY_TAG   246
#define LCNF_SARRAY_TAG  248
#define LCNF_STRING_TAG  249
#define LCNF_MPZ_TAG     250

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
  u64 large_free;        /* free list for >= 512-byte objects */
  u64 ba_empty;          /* cached persistent empty ByteArray */
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

/* Extended runtime block (`33688` bytes) matching `LcnfC0FullRt` (`scratch` + `scratch_cap`). */
#ifdef LCNF_C0RT
typedef struct {
  LcnfRt base;
  u64 scratch;
  u64 scratch_cap;
} LcnfC0RtBlock;
#else
typedef LcnfRt LcnfC0RtBlock;
#endif

/* Entry points called from LeanQbe.T code (all arguments / results are 64-bit). */
u64 lcnf_alloc(u64 rt, u64 sz);
void lcnf_dec_ref_cold(u64 rt, u64 o);
void lcnf_free_obj(u64 rt, u64 o);
void lcnf_mark_persistent(u64 rt, u64 o);
u64 lcnf_nat_slow(u64 rt, u64 op, u64 a, u64 b);
u64 lcnf_clo_under(u64 rt, u64 f, u64 k);
u64 lcnf_str_alloc(u64 rt, u64 byte_len, u64 char_len);
u64 lcnf_nat_alloc(u64 rt, u64 nlimbs);
u64 lcnf_nat_to_str(u64 rt, u64 n);
u64 lcnf_char_op(u64 rt, u64 op, u64 x);
u64 lcnf_oob(u64 rt, u64 dv);
u64 lcnf_array_mk_empty(u64 rt, u64 cap);
u64 lcnf_array_mk(u64 rt, u64 list);
u64 lcnf_array_to_list(u64 rt, u64 arr);
u64 lcnf_array_push(u64 rt, u64 arr, u64 v);
u64 lcnf_array_replicate(u64 rt, u64 n, u64 v);
u64 lcnf_array_get(u64 rt, u64 dv, u64 arr, u64 idx, u64 flags);
u64 lcnf_array_set(u64 rt, u64 arr, u64 idx, u64 v, u64 unboxed);
u64 lcnf_array_pop(u64 rt, u64 arr);
u64 lcnf_array_swap(u64 rt, u64 arr, u64 i, u64 j, u64 check_bounds);
u64 lcnf_string_push(u64 rt, u64 s, u64 c);
u64 lcnf_string_append(u64 rt, u64 s1, u64 s2);
u64 lcnf_string_to_list(u64 rt, u64 s);
u64 lcnf_string_mk(u64 rt, u64 cs);
u64 lcnf_string_cmp_op(u64 rt, u64 op, u64 s1, u64 s2);
u64 lcnf_string_pos_op(u64 rt, u64 op, u64 s, u64 i, u64 e);
u64 lcnf_ba_empty(u64 rt);
u64 lcnf_ba_mk_empty(u64 rt, u64 cap);
u64 lcnf_ba_mk(u64 rt, u64 arr);
u64 lcnf_ba_data(u64 rt, u64 ba);
u64 lcnf_ba_push(u64 rt, u64 ba, u64 b);
u64 lcnf_ba_get(u64 rt, u64 ba, u64 idx, u64 unboxed);
u64 lcnf_ba_set(u64 rt, u64 ba, u64 idx, u64 b, u64 unboxed);
u64 lcnf_ba_cmp_op(u64 rt, u64 op, u64 a, u64 b);
u64 lcnf_float_bin(u64 rt, u64 op, u64 a, u64 b);
u64 lcnf_float_un(u64 rt, u64 op, u64 a);
u64 lcnf_float_of_sci(u64 rt, u64 m, u64 neg, u64 e);
u64 lcnf_int_op(u64 rt, u64 op, u64 a, u64 b);
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
