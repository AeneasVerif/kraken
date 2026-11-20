/* lcnf_rt.c: Tier-0 C runtime for Lean 4 impure LCNF lowered to LeanQbe.T.
 *
 * - 64-bit `lean_object` headers: m_rc:i32 @0, m_cs_sz:u16 @4 (object bytes), m_other:u8 @6
 *   (number of object fields of a constructor), m_tag:u8 @7; closures keep fun_id @8,
 *   arity:u16 @16, num_fixed:u16 @18 and their captured objects @24.
 * - Size-class free-list allocator over bump-allocated chunks: freed slots are reused first.
 * - Iterative (explicit worklist) lcnf_dec_ref_cold and lcnf_mark_persistent: no recursion.
 * - Telemetry (allocs, frees, live, peak, persistent, reused, cold decs) for leak checks.
 *
 * Native builds use real pointers.  With -DLCNF_TQBE this file is #included into the PrintCpp
 * C++ driver after tqbe_rt.hpp; object memory then lives in the simulated `tqbe::Mem`.
 */
#ifndef LCNF_TQBE
#include "lcnf_rt.h"
#endif
#include <stdlib.h>
#include <string.h>

#ifdef LCNF_TQBE
static ::tqbe::Mem *lcnf_tqbe_mem = nullptr;
static LcnfState lcnf_tqbe_state;
static u64 lcnf_tqbe_next_chunk = 0x40000000ULL;
#define LCNF_FN(n) rt_##n
static inline u64 ld64(u64 a) {
  return ::tqbe::load<::tqbe::bits<64>>(*lcnf_tqbe_mem, ::tqbe::bits<64>(a)).word(0);
}
static inline u64 ld32(u64 a) {
  return ::tqbe::load<::tqbe::bits<32>>(*lcnf_tqbe_mem, ::tqbe::bits<64>(a)).word(0);
}
static inline u64 ld16(u64 a) {
  return ::tqbe::load<::tqbe::bits<16>>(*lcnf_tqbe_mem, ::tqbe::bits<64>(a)).word(0);
}
static inline u64 ld8(u64 a) {
  return ::tqbe::load<::tqbe::bits<8>>(*lcnf_tqbe_mem, ::tqbe::bits<64>(a)).word(0);
}
static inline void st64(u64 a, u64 v) {
  ::tqbe::store<::tqbe::bits<64>>(*lcnf_tqbe_mem, ::tqbe::bits<64>(a), ::tqbe::bits<64>(v));
}
static inline void st32(u64 a, u64 v) {
  ::tqbe::store<::tqbe::bits<32>>(*lcnf_tqbe_mem, ::tqbe::bits<64>(a), ::tqbe::bits<32>(v));
}
static inline void st16(u64 a, u64 v) {
  ::tqbe::store<::tqbe::bits<16>>(*lcnf_tqbe_mem, ::tqbe::bits<64>(a), ::tqbe::bits<16>(v));
}
LcnfState *lcnf_state(u64 rt) {
  (void)rt;
  return &lcnf_tqbe_state;
}
#else
#define LCNF_FN(n) n
static inline u64 ld64(u64 a) { u64 v; memcpy(&v, (void *)(uintptr_t)a, 8); return v; }
static inline u64 ld32(u64 a) { uint32_t v; memcpy(&v, (void *)(uintptr_t)a, 4); return v; }
static inline u64 ld16(u64 a) { uint16_t v; memcpy(&v, (void *)(uintptr_t)a, 2); return v; }
static inline u64 ld8(u64 a) { return *(uint8_t *)(uintptr_t)a; }
static inline void st64(u64 a, u64 v) { memcpy((void *)(uintptr_t)a, &v, 8); }
static inline void st32(u64 a, u64 v) {
  uint32_t w = (uint32_t)v;
  memcpy((void *)(uintptr_t)a, &w, 4);
}
static inline void st16(u64 a, u64 v) {
  uint16_t w = (uint16_t)v;
  memcpy((void *)(uintptr_t)a, &w, 2);
}
LcnfState *lcnf_state(u64 rt) { return &((LcnfRt *)(uintptr_t)rt)->s; }
#endif

#define LCNF_CHUNK (1ULL << 20)

static void lcnf_fatal(const char *msg) {
  fprintf(stderr, "lcnf_rt: fatal: %s\n", msg);
  exit(3);
}

static inline int is_scalar(u64 o) { return (o & 1ULL) != 0; }
static inline int32_t get_rc(u64 o) { return (int32_t)(uint32_t)ld32(o); }
static inline void set_rc(u64 o, int32_t rc) { st32(o, (u64)(uint32_t)rc); }
static inline u64 obj_bytes(u64 o) { return ld16(o + 4); }

/* Number of object fields and their offset. */
static inline void obj_fields(u64 o, u64 *n, u64 *off) {
  u64 tag = ld8(o + 7);
  if (tag == LCNF_CLOSURE_TAG) {
    *n = ld16(o + 18);
    *off = 24;
  } else if (tag <= 244) {
    *n = ld8(o + 6);
    *off = 8;
  } else {
    *n = 0;
    *off = 8;
  }
}

static void work_push(LcnfState *s, u64 *len, u64 o) {
  if (*len == s->work_cap) {
    u64 cap = s->work_cap ? 2 * s->work_cap : 1024;
    u64 *w = (u64 *)realloc(s->work, cap * sizeof(u64));
    if (!w) lcnf_fatal("worklist out of memory");
    s->work = w;
    s->work_cap = cap;
  }
  s->work[(*len)++] = o;
}

static void new_chunk(LcnfState *s) {
#ifdef LCNF_TQBE
  u64 base = lcnf_tqbe_next_chunk;
  lcnf_tqbe_next_chunk += LCNF_CHUNK + 4096;
  lcnf_tqbe_mem->alloc(base, LCNF_CHUNK, 0);
  s->cur = base;
  s->end = base + LCNF_CHUNK;
#else
  void *p = malloc(LCNF_CHUNK);
  if (!p) lcnf_fatal("heap out of memory");
  if (s->nchunks == s->chunks_cap) {
    u64 cap = s->chunks_cap ? 2 * s->chunks_cap : 16;
    void **c = (void **)realloc(s->chunks, cap * sizeof(void *));
    if (!c) lcnf_fatal("chunk table out of memory");
    s->chunks = c;
    s->chunks_cap = cap;
  }
  s->chunks[s->nchunks++] = p;
  s->cur = (u64)(uintptr_t)p;
  s->end = s->cur + LCNF_CHUNK;
#endif
}

u64 LCNF_FN(lcnf_alloc)(u64 rt, u64 sz) {
  LcnfState *s = lcnf_state(rt);
  u64 bytes = (sz + 7) & ~7ULL;
  u64 cls = bytes >> 3;
  if (cls >= LCNF_NUM_CLASSES || bytes < 16) lcnf_fatal("unsupported object size");
  u64 p = s->free_list[cls];
  if (p) {
    s->free_list[cls] = ld64(p + 8);
    s->st.reused++;
  } else {
    if (s->cur + bytes > s->end) new_chunk(s);
    p = s->cur;
    s->cur += bytes;
  }
  s->st.allocs++;
  s->st.bytes += bytes;
  s->st.live++;
  if (s->st.live > s->st.peak_live) s->st.peak_live = s->st.live;
  return p;
}

/* Return the cell of `o` (its fields are not touched) to its size-class free list. */
static void free_cell(LcnfState *s, u64 o) {
  u64 cls = obj_bytes(o) >> 3;
  if (cls >= LCNF_NUM_CLASSES || cls < 2) lcnf_fatal("free of corrupt object");
  st64(o, 0);
  st64(o + 8, s->free_list[cls]);
  s->free_list[cls] = o;
  s->st.frees++;
  s->st.live--;
}

/* `del o` (`lean_del_object`): free the cell of a dead object; tagged scalars are ignored. */
void LCNF_FN(lcnf_free_obj)(u64 rt, u64 o) {
  if (!is_scalar(o)) free_cell(lcnf_state(rt), o);
}

/* Called when the last reference to `o` is dropped (m_rc == 1): free `o` and, iteratively,
 * every object whose count drops to zero as a consequence. */
void LCNF_FN(lcnf_dec_ref_cold)(u64 rt, u64 o) {
  LcnfState *s = lcnf_state(rt);
  u64 len = 0;
  s->st.cold_decs++;
  work_push(s, &len, o);
  while (len > 0) {
    u64 x = s->work[--len];
    u64 n, off;
    obj_fields(x, &n, &off);
    for (u64 i = 0; i < n; i++) {
      u64 c = ld64(x + off + 8 * i);
      if (is_scalar(c)) continue;
      int32_t rc = get_rc(c);
      if (rc == 1) work_push(s, &len, c);
      else if (rc > 1) set_rc(c, rc - 1);
    }
    free_cell(s, x);
  }
}

/* Mark `o` and everything reachable from it persistent (m_rc = 0, immortal, never freed). */
void LCNF_FN(lcnf_mark_persistent)(u64 rt, u64 o) {
  LcnfState *s = lcnf_state(rt);
  u64 len = 0;
  if (is_scalar(o) || get_rc(o) == 0) return;
  set_rc(o, 0);
  s->st.persistent++;
  work_push(s, &len, o);
  while (len > 0) {
    u64 x = s->work[--len];
    u64 n, off;
    obj_fields(x, &n, &off);
    for (u64 i = 0; i < n; i++) {
      u64 c = ld64(x + off + 8 * i);
      if (is_scalar(c) || get_rc(c) == 0) continue;
      set_rc(c, 0);
      s->st.persistent++;
      work_push(s, &len, c);
    }
  }
}

static inline void inc_obj(u64 o) {
  if (is_scalar(o)) return;
  int32_t rc = get_rc(o);
  if (rc > 0) set_rc(o, rc + 1);
}

/* Under-application: a new closure with room for `k` more captured objects (the caller stores
 * them at 24 + 8 * (num_fixed + i)). */
u64 LCNF_FN(lcnf_clo_under)(u64 rt, u64 f, u64 k) {
  u64 nfix = ld16(f + 18);
  u64 n2 = nfix + k;
  u64 sz = 24 + 8 * n2;
  u64 c = LCNF_FN(lcnf_alloc)(rt, sz);
  st64(c, 1ULL | (sz << 32) | ((u64)LCNF_CLOSURE_TAG << 56));
  st64(c + 8, ld64(f + 8));
  st16(c + 16, ld16(f + 16));
  st16(c + 18, n2);
  st32(c + 20, 0);
  for (u64 i = 0; i < nfix; i++) st64(c + 24 + 8 * i, ld64(f + 24 + 8 * i));
  int32_t rc = get_rc(f);
  if (rc == 1) {
    free_cell(lcnf_state(rt), f);
  } else {
    for (u64 i = 0; i < nfix; i++) inc_obj(ld64(f + 24 + 8 * i));
    if (rc > 1) set_rc(f, rc - 1);
  }
  return c;
}

#ifdef LCNF_TQBE
#define LCNF_PANIC(code) \
  ::tqbe::exit_call("lcnf_panic", ::tqbe::bits<64>(rt), ::tqbe::bits<64>(code))
#else
#define LCNF_PANIC(code) lcnf_panic(rt, code)
#endif

/* Slow paths of the inline Nat fast paths.  This Tier-0 runtime has no big numbers: every
 * Nat is a tagged scalar, so reaching here means a result would leave the fixnum range. */
u64 LCNF_FN(lcnf_nat_slow)(u64 rt, u64 op, u64 a, u64 b) {
  fprintf(stderr, "lcnf_rt: Nat op %llu on %#llx, %#llx needs big numbers (unsupported)\n",
          (unsigned long long)op, (unsigned long long)a, (unsigned long long)b);
  LCNF_PANIC(100 + op);
#ifdef LCNF_TQBE
  return 1;
#endif
}

#ifndef LCNF_TQBE
void lcnf_panic(u64 rt, u64 code) {
  (void)rt;
  fprintf(stderr, "lcnf_rt: panic %llu (%s)\n", (unsigned long long)code,
          code == 1 ? "unreachable" : code == 2 ? "bad closure" : "Nat overflow");
  exit(4);
}
#endif

void lcnf_rt_init(u64 rt) {
  LcnfState *s = lcnf_state(rt);
  memset(s, 0, sizeof(*s));
#ifndef LCNF_TQBE
  memset((void *)(uintptr_t)rt, 0, LCNF_RT_T_BYTES);
#endif
}

void lcnf_rt_free(u64 rt) {
  LcnfState *s = lcnf_state(rt);
#ifndef LCNF_TQBE
  for (u64 i = 0; i < s->nchunks; i++) free(s->chunks[i]);
  free(s->chunks);
#endif
  free(s->work);
  memset(s, 0, sizeof(*s));
}

void lcnf_rt_print_stats(u64 rt, const char *tag, FILE *f) {
  LcnfStats *st = &lcnf_state(rt)->st;
  fprintf(f, "STAT %s allocs=%llu frees=%llu live=%llu peak=%llu persistent=%llu reused=%llu "
          "cold_decs=%llu bytes=%llu\n", tag, (unsigned long long)st->allocs,
          (unsigned long long)st->frees, (unsigned long long)st->live,
          (unsigned long long)st->peak_live, (unsigned long long)st->persistent,
          (unsigned long long)st->reused, (unsigned long long)st->cold_decs,
          (unsigned long long)st->bytes);
}
