/* lcnf_rt.c: Tier-0 C runtime for Lean 4 impure LCNF lowered to LeanQbe.T.
 *
 * - 64-bit `lean_object` headers: m_rc:i32 @0, m_cs_sz:u16 @4 (object bytes), m_other:u8 @6
 *   (number of object fields of a constructor, or elem_size for ScalarArray), m_tag:u8 @7.
 *   Closures (245): fun_id @8, arity:u16 @16, num_fixed:u16 @18, captured @24.
 *   Array (246): m_size @8, m_capacity @16, m_data @24.
 *   ScalarArray (248): m_size @8, m_capacity @16, m_data @24.
 *   String (249): m_size @8 (incl. NUL), m_capacity @16, m_length @24, m_data @32.
 *   MPZ (250): m_cap:u32 @8, m_len:u32 @12, limbs:u64[] @16 (canonical: >= 2^63).
 * - Size-class free-list allocator + large-object free list over bump-allocated chunks.
 * - Iterative lcnf_dec_ref_cold and lcnf_mark_persistent (no recursion).
 * - Telemetry (allocs, frees, live, peak, persistent, reused, cold decs) for leak checks.
 *
 * Native builds use real pointers. With -DLCNF_TQBE this file is #included into the PrintCpp
 * C++ driver after tqbe_rt.hpp; object memory then lives in the simulated `tqbe::Mem`.
 */
#ifndef LCNF_TQBE
#include "lcnf_rt.h"
#endif
#include <math.h>
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
static inline void st8(u64 a, u64 v) {
  ::tqbe::store<::tqbe::bits<8>>(*lcnf_tqbe_mem, ::tqbe::bits<64>(a), ::tqbe::bits<8>(v));
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
static inline void st8(u64 a, u64 v) { *(uint8_t *)(uintptr_t)a = (uint8_t)v; }
LcnfState *lcnf_state(u64 rt) { return &((LcnfRt *)(uintptr_t)rt)->s; }
#endif

#define LCNF_CHUNK (1ULL << 20)
typedef __uint128_t u128;

static void lcnf_fatal(const char *msg) {
  fprintf(stderr, "lcnf_rt: fatal: %s\n", msg);
  exit(3);
}

static inline int is_scalar(u64 o) { return (o & 1ULL) != 0; }
static inline u64 box_nat(u64 n) { return (n << 1) | 1ULL; }
static inline u64 unbox_nat(u64 o) { return o >> 1; }
static inline int32_t get_rc(u64 o) { return (int32_t)(uint32_t)ld32(o); }
static inline void set_rc(u64 o, int32_t rc) { st32(o, (u64)(uint32_t)rc); }
static inline int is_excl(u64 o) { return get_rc(o) == 1; }

static inline u64 obj_total_bytes(u64 o) {
  u64 tag = ld8(o + 7);
  if (tag == LCNF_ARRAY_TAG) return (24 + 8 * ld64(o + 16) + 7) & ~7ULL;
  if (tag == LCNF_SARRAY_TAG) {
    u64 esz = ld8(o + 6) & 0x7fULL;
    return (24 + esz * ld64(o + 16) + 7) & ~7ULL;
  }
  if (tag == LCNF_STRING_TAG) return (32 + ld64(o + 16) + 7) & ~7ULL;
  if (tag == LCNF_MPZ_TAG) return 16 + 8 * ld32(o + 8);
  return ld16(o + 4);
}

/* Number of object fields and their offset. */
static inline void obj_fields(u64 o, u64 *n, u64 *off) {
  u64 tag = ld8(o + 7);
  if (tag == LCNF_CLOSURE_TAG) {
    *n = ld16(o + 18);
    *off = 24;
  } else if (tag == LCNF_ARRAY_TAG) {
    *n = ld64(o + 8);
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

static u64 alloc_chunk(LcnfState *s, u64 sz) {
#ifdef LCNF_TQBE
  u64 base = lcnf_tqbe_next_chunk;
  lcnf_tqbe_next_chunk += sz + 4096;
  lcnf_tqbe_mem->alloc(base, sz, 0);
  (void)s;
  return base;
#else
  void *p = malloc(sz);
  if (!p) lcnf_fatal("heap out of memory");
  if (s->nchunks == s->chunks_cap) {
    u64 cap = s->chunks_cap ? 2 * s->chunks_cap : 16;
    void **c = (void **)realloc(s->chunks, cap * sizeof(void *));
    if (!c) lcnf_fatal("chunk table out of memory");
    s->chunks = c;
    s->chunks_cap = cap;
  }
  s->chunks[s->nchunks++] = p;
  return (u64)(uintptr_t)p;
#endif
}

static void new_chunk(LcnfState *s) {
  u64 base = alloc_chunk(s, LCNF_CHUNK);
  s->cur = base;
  s->end = base + LCNF_CHUNK;
}

u64 LCNF_FN(lcnf_alloc)(u64 rt, u64 sz) {
  LcnfState *s = lcnf_state(rt);
  u64 bytes = (sz + 7) & ~7ULL;
  if (bytes < 16) lcnf_fatal("unsupported object size");
  u64 cls = bytes >> 3;
  u64 p = 0;
  if (cls < LCNF_NUM_CLASSES) {
    p = s->free_list[cls];
    if (p) {
      s->free_list[cls] = ld64(p + 8);
      s->st.reused++;
    } else {
      if (s->cur + bytes > s->end) new_chunk(s);
      p = s->cur;
      s->cur += bytes;
    }
  } else {
    u64 prev = 0, cur = s->large_free;
    while (cur) {
      if (ld64(cur + 16) == bytes) {
        u64 nxt = ld64(cur + 8);
        if (prev) st64(prev + 8, nxt);
        else s->large_free = nxt;
        p = cur;
        s->st.reused++;
        break;
      }
      prev = cur;
      cur = ld64(cur + 8);
    }
    if (!p) {
      if (bytes <= LCNF_CHUNK) {
        if (s->cur + bytes > s->end) new_chunk(s);
        p = s->cur;
        s->cur += bytes;
      } else {
        p = alloc_chunk(s, bytes);
      }
    }
  }
  s->st.allocs++;
  s->st.bytes += bytes;
  s->st.live++;
  if (s->st.live > s->st.peak_live) s->st.peak_live = s->st.live;
  return p;
}

/* Return the cell of `o` (its fields are not touched) to its free list. */
static void free_cell(LcnfState *s, u64 o) {
  u64 bytes = obj_total_bytes(o);
  u64 cls = bytes >> 3;
  if (cls < 2) lcnf_fatal("free of corrupt object");
  st64(o, 0);
  if (cls < LCNF_NUM_CLASSES) {
    st64(o + 8, s->free_list[cls]);
    s->free_list[cls] = o;
  } else {
    st64(o + 8, s->large_free);
    st64(o + 16, bytes);
    s->large_free = o;
  }
  s->st.frees++;
  s->st.live--;
}

void LCNF_FN(lcnf_free_obj)(u64 rt, u64 o) {
  if (!is_scalar(o)) free_cell(lcnf_state(rt), o);
}

static inline void dfs_walk(LcnfState *s, u64 o, int persist) {
  u64 len = 0;
  work_push(s, &len, o);
  while (len > 0) {
    u64 x = s->work[--len], n, off;
    obj_fields(x, &n, &off);
    for (u64 i = 0; i < n; i++) {
      u64 c = ld64(x + off + 8 * i);
      if (is_scalar(c)) continue;
      int32_t rc = get_rc(c);
      if (persist) {
        if (rc != 0) { set_rc(c, 0); s->st.persistent++; work_push(s, &len, c); }
      } else if (rc == 1) work_push(s, &len, c);
      else if (rc > 1) set_rc(c, rc - 1);
    }
    if (!persist) free_cell(s, x);
  }
}

void LCNF_FN(lcnf_dec_ref_cold)(u64 rt, u64 o) {
  LcnfState *s = lcnf_state(rt);
  s->st.cold_decs++;
  dfs_walk(s, o, 0);
}

void LCNF_FN(lcnf_mark_persistent)(u64 rt, u64 o) {
  LcnfState *s = lcnf_state(rt);
  if (is_scalar(o) || get_rc(o) == 0) return;
  set_rc(o, 0);
  s->st.persistent++;
  dfs_walk(s, o, 1);
}

static inline void inc_obj(u64 o) {
  if (is_scalar(o)) return;
  int32_t rc = get_rc(o);
  if (rc > 0) set_rc(o, rc + 1);
}

static inline void inc_obj_n(u64 o, u64 n) {
  if (is_scalar(o) || n == 0) return;
  int32_t rc = get_rc(o);
  if (rc > 0) set_rc(o, rc + (int32_t)n);
}

static inline void dec_obj(u64 rt, u64 o) {
  if (is_scalar(o)) return;
  int32_t rc = get_rc(o);
  if (rc == 1) LCNF_FN(lcnf_dec_ref_cold)(rt, o);
  else if (rc > 1) set_rc(o, rc - 1);
}

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

/* ---- Arbitrary-precision Nat (LeanMPZ) ---- */

u64 LCNF_FN(lcnf_nat_alloc)(u64 rt, u64 nlimbs) {
  if (nlimbs == 0) nlimbs = 1;
  u64 sz = 16 + 8 * nlimbs;
  u64 p = LCNF_FN(lcnf_alloc)(rt, sz);
  u64 cs = sz < 65536 ? sz : 0;
  st64(p, 1ULL | (cs << 32) | ((u64)LCNF_MPZ_TAG << 56));
  st32(p + 8, nlimbs);
  st32(p + 12, nlimbs);
  return p;
}

typedef struct {
  u64 *d;
  uint32_t n;
  u64 inline_buf[8];
  int heap;
} NatView;

static void nat_view(u64 x, NatView *v) {
  v->heap = 0;
  if (is_scalar(x)) {
    u64 u = unbox_nat(x);
    v->inline_buf[0] = u;
    v->d = v->inline_buf;
    v->n = u ? 1 : 0;
    return;
  }
  uint32_t len = (uint32_t)ld32(x + 12);
  v->n = len;
#ifndef LCNF_TQBE
  v->d = (u64 *)(uintptr_t)(x + 16);
#else
  if (len <= 8) {
    v->d = v->inline_buf;
  } else {
    v->d = (u64 *)malloc(len * sizeof(u64));
    if (!v->d) lcnf_fatal("nat_view out of memory");
    v->heap = 1;
  }
  for (uint32_t i = 0; i < len; i++) v->d[i] = ld64(x + 16 + 8 * i);
#endif
}

static void nat_view_free(NatView *v) {
  if (v->heap) free(v->d);
}

static uint32_t trim_limbs(const u64 *d, uint32_t n) {
  while (n > 0 && d[n - 1] == 0) n--;
  return n;
}

static u64 nat_from_limbs(u64 rt, const u64 *d, uint32_t n) {
  n = trim_limbs(d, n);
  if (n == 0) return box_nat(0);
  if (n == 1 && d[0] < (1ULL << 63)) return box_nat(d[0]);
  u64 p = LCNF_FN(lcnf_nat_alloc)(rt, n);
  for (uint32_t i = 0; i < n; i++) st64(p + 16 + 8 * i, d[i]);
  return p;
}

static int cmp_limbs(const u64 *a, uint32_t na, const u64 *b, uint32_t nb) {
  if (na != nb) return na < nb ? -1 : 1;
  for (uint32_t i = na; i-- > 0;) {
    if (a[i] != b[i]) return a[i] < b[i] ? -1 : 1;
  }
  return 0;
}

static u64 *alloc_limbs(uint32_t n) {
  u64 *p = (u64 *)calloc(n ? n : 1, sizeof(u64));
  if (!p) lcnf_fatal("bignum out of memory");
  return p;
}

static uint32_t add_limbs(const u64 *a, uint32_t na, const u64 *b, uint32_t nb, u64 *out) {
  uint32_t m = na > nb ? na : nb;
  u128 carry = 0;
  for (uint32_t i = 0; i < m; i++) {
    u128 s = carry + (i < na ? a[i] : 0) + (i < nb ? b[i] : 0);
    out[i] = (u64)s;
    carry = s >> 64;
  }
  if (carry) {
    out[m] = (u64)carry;
    return m + 1;
  }
  return trim_limbs(out, m);
}

static uint32_t sub_limbs(const u64 *a, uint32_t na, const u64 *b, uint32_t nb, u64 *out) {
  if (cmp_limbs(a, na, b, nb) <= 0) return 0;
  u128 borrow = 0;
  for (uint32_t i = 0; i < na; i++) {
    u128 av = a[i];
    u128 bv = (i < nb ? (u128)b[i] : 0) + borrow;
    if (av >= bv) {
      out[i] = (u64)(av - bv);
      borrow = 0;
    } else {
      out[i] = (u64)((((u128)1 << 64) + av) - bv);
      borrow = 1;
    }
  }
  return trim_limbs(out, na);
}

static uint32_t mul_limbs(const u64 *a, uint32_t na, const u64 *b, uint32_t nb, u64 *out) {
  if (na == 0 || nb == 0) return 0;
  memset(out, 0, (na + nb) * sizeof(u64));
  for (uint32_t i = 0; i < na; i++) {
    u128 carry = 0;
    for (uint32_t j = 0; j < nb; j++) {
      u128 p = (u128)a[i] * (u128)b[j] + out[i + j] + carry;
      out[i + j] = (u64)p;
      carry = p >> 64;
    }
    out[i + nb] += (u64)carry;
  }
  return trim_limbs(out, na + nb);
}

static uint32_t bitlen_limbs(const u64 *a, uint32_t na) {
  if (na == 0) return 0;
  u64 top = a[na - 1];
  uint32_t b = (na - 1) * 64;
  while (top) { b++; top >>= 1; }
  return b;
}

static void divmod_limbs(const u64 *a, uint32_t na, const u64 *b, uint32_t nb,
                         u64 *q, uint32_t *qn, u64 *r, uint32_t *rn) {
  if (nb == 0) {
    *qn = 0;
    if (na) memcpy(r, a, na * sizeof(u64));
    *rn = na;
    return;
  }
  if (cmp_limbs(a, na, b, nb) < 0) {
    *qn = 0;
    if (na) memcpy(r, a, na * sizeof(u64));
    *rn = na;
    return;
  }
  if (nb == 1) {
    u64 d = b[0];
    u128 rem = 0;
    for (uint32_t i = na; i-- > 0;) {
      u128 cur = (rem << 64) | a[i];
      q[i] = (u64)(cur / d);
      rem = cur % d;
    }
    *qn = trim_limbs(q, na);
    r[0] = (u64)rem;
    *rn = rem ? 1 : 0;
    return;
  }
  memset(q, 0, na * sizeof(u64));
  memset(r, 0, (nb + 1) * sizeof(u64));
  uint32_t cur_rn = 0;
  uint32_t bits = bitlen_limbs(a, na);
  for (uint32_t bit = bits; bit-- > 0;) {
    u64 carry = (a[bit / 64] >> (bit % 64)) & 1ULL;
    for (uint32_t i = 0; i < cur_rn; i++) {
      u64 next_c = r[i] >> 63;
      r[i] = (r[i] << 1) | carry;
      carry = next_c;
    }
    if (carry) r[cur_rn++] = carry;
    cur_rn = trim_limbs(r, cur_rn);
    if (cmp_limbs(r, cur_rn, b, nb) >= 0) {
      cur_rn = sub_limbs(r, cur_rn, b, nb, r);
      q[bit / 64] |= 1ULL << (bit % 64);
    }
  }
  *qn = trim_limbs(q, na);
  *rn = cur_rn;
}

static u64 nat_shift_left(u64 rt, const NatView *va, u64 shift) {
  if (va->n == 0 || shift == 0) return nat_from_limbs(rt, va->d, va->n);
  if (shift > (1ULL << 24)) lcnf_fatal("Nat.shiftLeft too large");
  uint32_t wshift = (uint32_t)(shift / 64);
  uint32_t bshift = (uint32_t)(shift % 64);
  uint32_t out_n = va->n + wshift + 1;
  u64 *out = alloc_limbs(out_n);
  if (bshift == 0) {
    memcpy(out + wshift, va->d, va->n * sizeof(u64));
  } else {
    u64 carry = 0;
    for (uint32_t i = 0; i < va->n; i++) {
      out[i + wshift] = (va->d[i] << bshift) | carry;
      carry = va->d[i] >> (64 - bshift);
    }
    out[va->n + wshift] = carry;
  }
  u64 res = nat_from_limbs(rt, out, out_n);
  free(out);
  return res;
}

static u64 nat_shift_right(u64 rt, const NatView *va, u64 shift) {
  uint32_t wshift = (uint32_t)(shift / 64);
  uint32_t bshift = (uint32_t)(shift % 64);
  if (shift > (1ULL << 30) || wshift >= va->n) return box_nat(0);
  uint32_t out_n = va->n - wshift;
  u64 *out = alloc_limbs(out_n);
  if (bshift == 0) {
    memcpy(out, va->d + wshift, out_n * sizeof(u64));
  } else {
    for (uint32_t i = 0; i < out_n; i++) {
      u64 hi = (i + 1 < out_n) ? (va->d[i + wshift + 1] << (64 - bshift)) : 0;
      out[i] = (va->d[i + wshift] >> bshift) | hi;
    }
  }
  u64 res = nat_from_limbs(rt, out, out_n);
  free(out);
  return res;
}

static u64 nat_pow_op(u64 rt, const NatView *va, const NatView *vb) {
  if (vb->n == 0) return box_nat(1);
  if (va->n == 0) return box_nat(0);
  if (va->n == 1 && va->d[0] == 1) return box_nat(1);
  if (vb->n > 1 || vb->d[0] > (1ULL << 20)) lcnf_fatal("Nat.pow exponent too large");
  u64 exp = vb->d[0];
  u64 *base = alloc_limbs(va->n);
  memcpy(base, va->d, va->n * sizeof(u64));
  uint32_t bn = va->n;
  u64 *res = alloc_limbs(1);
  res[0] = 1;
  uint32_t rn = 1;
  while (exp > 0) {
    if (exp & 1ULL) {
      u64 *tmp = alloc_limbs(rn + bn);
      uint32_t tn = mul_limbs(res, rn, base, bn, tmp);
      free(res);
      res = tmp;
      rn = tn;
    }
    exp >>= 1;
    if (exp > 0) {
      u64 *tmp = alloc_limbs(bn + bn);
      uint32_t tn = mul_limbs(base, bn, base, bn, tmp);
      free(base);
      base = tmp;
      bn = tn;
    }
  }
  u64 out = nat_from_limbs(rt, res, rn);
  free(base);
  free(res);
  return out;
}

static u64 nat_gcd_op(u64 rt, const NatView *va, const NatView *vb) {
  if (va->n == 0) return nat_from_limbs(rt, vb->d, vb->n);
  if (vb->n == 0) return nat_from_limbs(rt, va->d, va->n);
  uint32_t an = va->n, bn = vb->n;
  u64 *a = alloc_limbs(an), *b = alloc_limbs(bn);
  memcpy(a, va->d, an * sizeof(u64));
  memcpy(b, vb->d, bn * sizeof(u64));
  while (bn > 0) {
    u64 *q = alloc_limbs(an), *r = alloc_limbs(bn + 1);
    uint32_t qn = 0, rn = 0;
    divmod_limbs(a, an, b, bn, q, &qn, r, &rn);
    free(q);
    free(a);
    a = b;
    an = bn;
    b = r;
    bn = rn;
  }
  u64 out = nat_from_limbs(rt, a, an);
  free(a);
  free(b);
  return out;
}

u64 LCNF_FN(lcnf_nat_slow)(u64 rt, u64 op, u64 a, u64 b) {
  if (op == 14) { /* toNat: raw u64 -> Nat */
    return nat_from_limbs(rt, &a, a ? 1 : 0);
  }
  NatView va, vb;
  nat_view(a, &va);
  if (op == 13) { /* ofNat: a=Nat, b=width */
    u64 lo = va.n ? va.d[0] : 0;
    nat_view_free(&va);
    if (b >= 64) return lo;
    return lo & ((1ULL << b) - 1ULL);
  }
  if (op == 17) { /* pred */
    u64 one = 1;
    u64 *out = alloc_limbs(va.n);
    uint32_t on = sub_limbs(va.d, va.n, &one, 1, out);
    u64 r = nat_from_limbs(rt, out, on);
    free(out);
    nat_view_free(&va);
    return r;
  }
  if (op == 19) { /* log2 */
    uint32_t bl = bitlen_limbs(va.d, va.n);
    nat_view_free(&va);
    return box_nat(bl ? bl - 1 : 0);
  }
  nat_view(b, &vb);
  u64 res = box_nat(0);
  switch (op) {
    case 1: { /* add */
      uint32_t cap = (va.n > vb.n ? va.n : vb.n) + 1;
      u64 *out = alloc_limbs(cap);
      uint32_t on = add_limbs(va.d, va.n, vb.d, vb.n, out);
      res = nat_from_limbs(rt, out, on);
      free(out);
      break;
    }
    case 2: { /* sub */
      u64 *out = alloc_limbs(va.n);
      uint32_t on = sub_limbs(va.d, va.n, vb.d, vb.n, out);
      res = nat_from_limbs(rt, out, on);
      free(out);
      break;
    }
    case 3: { /* mul */
      u64 *out = alloc_limbs(va.n + vb.n);
      uint32_t on = mul_limbs(va.d, va.n, vb.d, vb.n, out);
      res = nat_from_limbs(rt, out, on);
      free(out);
      break;
    }
    case 4: case 5: { /* div / mod */
      u64 *q = alloc_limbs(va.n), *r = alloc_limbs((va.n > vb.n ? va.n : vb.n) + 1);
      uint32_t qn = 0, rn = 0;
      divmod_limbs(va.d, va.n, vb.d, vb.n, q, &qn, r, &rn);
      res = nat_from_limbs(rt, op == 4 ? q : r, op == 4 ? qn : rn);
      free(q);
      free(r);
      break;
    }
    case 6: res = cmp_limbs(va.d, va.n, vb.d, vb.n) == 0 ? 1 : 0; break;
    case 7: res = cmp_limbs(va.d, va.n, vb.d, vb.n) < 0 ? 1 : 0; break;
    case 8: res = cmp_limbs(va.d, va.n, vb.d, vb.n) <= 0 ? 1 : 0; break;
    case 9: { /* shiftRight */
      u64 sh = vb.n == 0 ? 0 : (vb.n == 1 ? vb.d[0] : (1ULL << 32));
      res = nat_shift_right(rt, &va, sh);
      break;
    }
    case 10: case 11: case 12: { /* land, lor, xor */
      uint32_t m = op == 10 ? (va.n < vb.n ? va.n : vb.n) : (va.n > vb.n ? va.n : vb.n);
      u64 *out = alloc_limbs(m);
      for (uint32_t i = 0; i < m; i++) {
        u64 av = i < va.n ? va.d[i] : 0;
        u64 bv = i < vb.n ? vb.d[i] : 0;
        out[i] = op == 10 ? (av & bv) : (op == 11 ? (av | bv) : (av ^ bv));
      }
      res = nat_from_limbs(rt, out, m);
      free(out);
      break;
    }
    case 15: { /* shiftLeft */
      if (vb.n > 1) lcnf_fatal("Nat.shiftLeft shift too large");
      res = nat_shift_left(rt, &va, vb.n ? vb.d[0] : 0);
      break;
    }
    case 16: res = nat_pow_op(rt, &va, &vb); break;
    case 18: res = nat_gcd_op(rt, &va, &vb); break;
    default:
      nat_view_free(&va);
      nat_view_free(&vb);
      LCNF_PANIC(100 + op);
  }
  nat_view_free(&va);
  nat_view_free(&vb);
  return res;
}

/* ---- Strings ---- */

u64 LCNF_FN(lcnf_str_alloc)(u64 rt, u64 byte_len, u64 char_len) {
  u64 cap = byte_len + 1;
  u64 sz = (32 + cap + 7) & ~7ULL;
  u64 p = LCNF_FN(lcnf_alloc)(rt, sz);
  st64(p, 1ULL | ((u64)LCNF_STRING_TAG << 56));
  st64(p + 8, cap);
  st64(p + 16, cap);
  st64(p + 24, char_len);
  st8(p + 32 + byte_len, 0);
  return p;
}

static u64 str_alloc_cap(u64 rt, u64 byte_len, u64 cap, u64 char_len) {
  if (cap < byte_len + 1) cap = byte_len + 1;
  u64 sz = (32 + cap + 7) & ~7ULL;
  u64 p = LCNF_FN(lcnf_alloc)(rt, sz);
  st64(p, 1ULL | ((u64)LCNF_STRING_TAG << 56));
  st64(p + 8, byte_len + 1);
  st64(p + 16, cap);
  st64(p + 24, char_len);
  st8(p + 32 + byte_len, 0);
  return p;
}

static void mem_copy_bytes(u64 dst, u64 src, u64 len) {
#ifndef LCNF_TQBE
  if (len) memcpy((void *)(uintptr_t)dst, (const void *)(uintptr_t)src, len);
#else
  for (u64 i = 0; i < len; i++) st8(dst + i, ld8(src + i));
#endif
}

static char *nat_to_ascii(u64 n, size_t *out_len) {
  if (is_scalar(n)) {
    char buf[32];
    int k = snprintf(buf, sizeof(buf), "%llu", (unsigned long long)unbox_nat(n));
    char *s = (char *)malloc((size_t)k + 1);
    if (!s) lcnf_fatal("nat_to_ascii out of memory");
    memcpy(s, buf, (size_t)k + 1);
    *out_len = (size_t)k;
    return s;
  }
  NatView va;
  nat_view(n, &va);
  u64 *cur = alloc_limbs(va.n);
  memcpy(cur, va.d, va.n * sizeof(u64));
  uint32_t cn = va.n;
  nat_view_free(&va);
  size_t cap = (size_t)cn * 20 + 4, len = 0;
  char *rev = (char *)malloc(cap);
  if (!rev) lcnf_fatal("nat_to_ascii out of memory");
  while (cn > 0) {
    u128 rem = 0;
    for (uint32_t i = cn; i-- > 0;) {
      u128 v = (rem << 64) | cur[i];
      cur[i] = (u64)(v / 1000000000ULL);
      rem = v % 1000000000ULL;
    }
    cn = trim_limbs(cur, cn);
    u64 chunk = (u64)rem;
    if (cn > 0) {
      for (int d = 0; d < 9; d++) {
        rev[len++] = (char)('0' + (chunk % 10));
        chunk /= 10;
      }
    } else {
      do {
        rev[len++] = (char)('0' + (chunk % 10));
        chunk /= 10;
      } while (chunk > 0);
    }
  }
  free(cur);
  char *out = (char *)malloc(len + 1);
  if (!out) lcnf_fatal("nat_to_ascii out of memory");
  for (size_t i = 0; i < len; i++) out[i] = rev[len - 1 - i];
  out[len] = 0;
  free(rev);
  *out_len = len;
  return out;
}

u64 LCNF_FN(lcnf_nat_to_str)(u64 rt, u64 n) {
  size_t len = 0;
  char *buf = nat_to_ascii(n, &len);
  dec_obj(rt, n);
  u64 s = LCNF_FN(lcnf_str_alloc)(rt, len, len);
  for (size_t i = 0; i < len; i++) st8(s + 32 + i, (uint8_t)buf[i]);
  free(buf);
  return s;
}

u64 LCNF_FN(lcnf_char_op)(u64 rt, u64 op, u64 x) {
  (void)rt;
  if (op == 0) { /* Char.ofNat (@&n) */
    if (!is_scalar(x)) return 0;
    u64 v = unbox_nat(x);
    return (v < 0xd800ULL || (v >= 0xe000ULL && v < 0x110000ULL)) ? v : 0;
  }
  /* Char.utf8Size */
  uint32_t c = (uint32_t)x;
  u64 sz = c < 0x80 ? 1 : c < 0x800 ? 2 : c < 0x10000 ? 3 : 4;
  return box_nat(sz);
}

u64 LCNF_FN(lcnf_oob)(u64 rt, u64 dv) {
  (void)rt;
  inc_obj(dv);
  return dv;
}

static unsigned utf8_encode(uint32_t c, uint8_t out[4]) {
  if (c < 0x80) { out[0] = (uint8_t)c; return 1; }
  if (c < 0x800) {
    out[0] = (uint8_t)(0xc0 | (c >> 6));
    out[1] = (uint8_t)(0x80 | (c & 0x3f));
    return 2;
  }
  if (c < 0x10000) {
    out[0] = (uint8_t)(0xe0 | (c >> 12));
    out[1] = (uint8_t)(0x80 | ((c >> 6) & 0x3f));
    out[2] = (uint8_t)(0x80 | (c & 0x3f));
    return 3;
  }
  out[0] = (uint8_t)(0xf0 | (c >> 18));
  out[1] = (uint8_t)(0x80 | ((c >> 12) & 0x3f));
  out[2] = (uint8_t)(0x80 | ((c >> 6) & 0x3f));
  out[3] = (uint8_t)(0x80 | (c & 0x3f));
  return 4;
}

static uint32_t utf8_decode_at(u64 s, u64 idx, u64 sz_bytes, u64 *step) {
  if (idx >= sz_bytes) { *step = 0; return 0; }
  uint8_t c0 = (uint8_t)ld8(s + 32 + idx);
  if ((c0 & 0x80) == 0) { *step = 1; return c0; }
  if ((c0 & 0xe0) == 0xc0 && idx + 1 < sz_bytes) {
    *step = 2;
    return ((uint32_t)(c0 & 0x1f) << 6) | (uint32_t)(ld8(s + 32 + idx + 1) & 0x3f);
  }
  if ((c0 & 0xf0) == 0xe0 && idx + 2 < sz_bytes) {
    *step = 3;
    return ((uint32_t)(c0 & 0x0f) << 12) | ((uint32_t)(ld8(s + 32 + idx + 1) & 0x3f) << 6) |
           (uint32_t)(ld8(s + 32 + idx + 2) & 0x3f);
  }
  if ((c0 & 0xf8) == 0xf0 && idx + 3 < sz_bytes) {
    *step = 4;
    return ((uint32_t)(c0 & 0x07) << 18) | ((uint32_t)(ld8(s + 32 + idx + 1) & 0x3f) << 12) |
           ((uint32_t)(ld8(s + 32 + idx + 2) & 0x3f) << 6) |
           (uint32_t)(ld8(s + 32 + idx + 3) & 0x3f);
  }
  *step = 1;
  return 0;
}

u64 LCNF_FN(lcnf_string_push)(u64 rt, u64 s, u64 c) {
  uint8_t enc[4];
  unsigned n = utf8_encode((uint32_t)c, enc);
  u64 sz = ld64(s + 8);
  u64 cap = ld64(s + 16);
  u64 clen = ld64(s + 24);
  if (is_excl(s) && sz + n <= cap) {
    for (unsigned i = 0; i < n; i++) st8(s + 32 + sz - 1 + i, enc[i]);
    st8(s + 32 + sz - 1 + n, 0);
    st64(s + 8, sz + n);
    st64(s + 24, clen + 1);
    return s;
  }
  u64 new_len = sz - 1 + n;
  u64 new_cap = cap * 2;
  if (new_cap < new_len + 1) new_cap = new_len + 1;
  u64 r = str_alloc_cap(rt, new_len, new_cap, clen + 1);
  mem_copy_bytes(r + 32, s + 32, sz - 1);
  for (unsigned i = 0; i < n; i++) st8(r + 32 + sz - 1 + i, enc[i]);
  dec_obj(rt, s);
  return r;
}

u64 LCNF_FN(lcnf_string_append)(u64 rt, u64 s1, u64 s2) {
  u64 sz1 = ld64(s1 + 8), sz2 = ld64(s2 + 8);
  u64 len1 = sz1 - 1, len2 = sz2 - 1;
  if (len2 == 0) return s1;
  u64 cap1 = ld64(s1 + 16);
  u64 clen = ld64(s1 + 24) + ld64(s2 + 24);
  if (is_excl(s1) && sz1 + len2 <= cap1) {
    mem_copy_bytes(s1 + 32 + len1, s2 + 32, len2 + 1);
    st64(s1 + 8, sz1 + len2);
    st64(s1 + 24, clen);
    return s1;
  }
  u64 new_len = len1 + len2;
  u64 new_cap = new_len + 1;
  if (is_excl(s1) && cap1 * 2 > new_cap) new_cap = cap1 * 2;
  u64 r = str_alloc_cap(rt, new_len, new_cap, clen);
  mem_copy_bytes(r + 32, s1 + 32, len1);
  mem_copy_bytes(r + 32 + len1, s2 + 32, len2 + 1);
  dec_obj(rt, s1);
  return r;
}

u64 LCNF_FN(lcnf_string_to_list)(u64 rt, u64 s) {
  u64 len = ld64(s + 8) - 1;
  u64 clen = ld64(s + 24);
  uint32_t *cps = clen ? (uint32_t *)malloc(clen * sizeof(uint32_t)) : NULL;
  if (clen && !cps) lcnf_fatal("string_to_list out of memory");
  u64 pos = 0, k = 0;
  while (pos < len && k < clen) {
    u64 step = 0;
    cps[k++] = utf8_decode_at(s, pos, len, &step);
    pos += step ? step : 1;
  }
  dec_obj(rt, s);
  u64 list = 1ULL; /* List.nil */
  u64 hdr = 1ULL | (24ULL << 32) | (2ULL << 48) | (1ULL << 56);
  for (u64 i = k; i-- > 0;) {
    u64 node = LCNF_FN(lcnf_alloc)(rt, 24);
    st64(node, hdr);
    st64(node + 8, box_nat(cps[i]));
    st64(node + 16, list);
    list = node;
  }
  free(cps);
  return list;
}

u64 LCNF_FN(lcnf_string_mk)(u64 rt, u64 cs) {
  u64 bytes = 0, chars = 0, cur = cs;
  uint8_t tmp[4];
  while (!is_scalar(cur)) {
    uint32_t cp = (uint32_t)unbox_nat(ld64(cur + 8));
    bytes += utf8_encode(cp, tmp);
    chars++;
    cur = ld64(cur + 16);
  }
  u64 s = LCNF_FN(lcnf_str_alloc)(rt, bytes, chars);
  u64 off = 0;
  cur = cs;
  while (!is_scalar(cur)) {
    uint32_t cp = (uint32_t)unbox_nat(ld64(cur + 8));
    unsigned n = utf8_encode(cp, tmp);
    for (unsigned i = 0; i < n; i++) st8(s + 32 + off + i, tmp[i]);
    off += n;
    cur = ld64(cur + 16);
  }
  dec_obj(rt, cs);
  return s;
}

static int cmp_byte_slices(u64 a, u64 la, u64 b, u64 lb) {
  u64 m = la < lb ? la : lb;
  for (u64 i = 0; i < m; i++) {
    uint8_t x = (uint8_t)ld8(a + i), y = (uint8_t)ld8(b + i);
    if (x != y) return x < y ? -1 : 1;
  }
  if (la != lb) return la < lb ? -1 : 1;
  return 0;
}

u64 LCNF_FN(lcnf_string_cmp_op)(u64 rt, u64 op, u64 s1, u64 s2) {
  (void)rt;
  if (s1 == s2) return op == 0 ? 1 : (op == 1 ? 0 : 1);
  u64 l1 = ld64(s1 + 8) - 1, l2 = ld64(s2 + 8) - 1;
  if (op == 0) {
    if (l1 != l2) return 0;
    return cmp_byte_slices(s1 + 32, l1, s2 + 32, l2) == 0 ? 1 : 0;
  }
  int c = cmp_byte_slices(s1 + 32, l1, s2 + 32, l2);
  if (op == 1) return c < 0 ? 1 : 0;
  return c < 0 ? 0 : (c == 0 ? 1 : 2);
}

u64 LCNF_FN(lcnf_string_pos_op)(u64 rt, u64 op, u64 s, u64 i, u64 e) {
  u64 sz = ld64(s + 8) - 1;
  if (op == 2) { /* atEnd */
    return (!is_scalar(i) || unbox_nat(i) >= sz) ? 1 : 0;
  }
  u64 idx = is_scalar(i) ? unbox_nat(i) : sz;
  if (op == 0) { /* utf8_get */
    u64 step = 0;
    return utf8_decode_at(s, idx, sz, &step);
  }
  if (op == 1) { /* utf8_next */
    if (idx >= sz) return box_nat(idx);
    u64 step = 0;
    (void)utf8_decode_at(s, idx, sz, &step);
    return box_nat(idx + (step ? step : 1));
  }
  if (op == 3) { /* utf8_extract */
    u64 b = is_scalar(i) ? unbox_nat(i) : sz;
    u64 end = is_scalar(e) ? unbox_nat(e) : sz;
    if (b >= end || b >= sz) return LCNF_FN(lcnf_str_alloc)(rt, 0, 0);
    if (end > sz) end = sz;
    u64 blen = end - b;
    u64 chars = 0, p = b;
    while (p < end) {
      u64 step = 0;
      (void)utf8_decode_at(s, p, end, &step);
      p += step ? step : 1;
      chars++;
    }
    u64 r = LCNF_FN(lcnf_str_alloc)(rt, blen, chars);
    mem_copy_bytes(r + 32, s + 32 + b, blen);
    return r;
  }
  if (op == 4) { /* get_byte */
    return idx < sz ? ld8(s + 32 + idx) : 0;
  }
  if (op == 5) { /* isValid */
    if (!is_scalar(i) || idx > sz) return 0;
    if (idx == sz) return 1;
    return (ld8(s + 32 + idx) & 0xc0) != 0x80 ? 1 : 0;
  }
  return 0;
}

/* ---- Arrays ---- */

static u64 alloc_array(u64 rt, u64 size, u64 cap) {
  u64 sz = 24 + 8 * cap;
  u64 p = LCNF_FN(lcnf_alloc)(rt, sz);
  st64(p, 1ULL | ((u64)LCNF_ARRAY_TAG << 56));
  st64(p + 8, size);
  st64(p + 16, cap);
  return p;
}

static u64 ensure_exclusive_array(u64 rt, u64 a, int expand) {
  u64 sz = ld64(a + 8), cap = ld64(a + 16);
  if (is_excl(a) && (!expand || sz < cap)) return a;
  u64 new_cap = expand ? (cap == 0 ? 4 : (sz < cap ? cap : cap * 2)) : cap;
  u64 r = alloc_array(rt, sz, new_cap);
  int excl = is_excl(a);
  for (u64 i = 0; i < sz; i++) {
    u64 v = ld64(a + 24 + 8 * i);
    if (!excl) inc_obj(v);
    st64(r + 24 + 8 * i, v);
  }
  if (excl) free_cell(lcnf_state(rt), a);
  else dec_obj(rt, a);
  return r;
}

u64 LCNF_FN(lcnf_array_mk_empty)(u64 rt, u64 cap) {
  u64 c = is_scalar(cap) ? unbox_nat(cap) : 0;
  return alloc_array(rt, 0, c);
}

u64 LCNF_FN(lcnf_array_mk)(u64 rt, u64 list) {
  u64 n = 0, cur = list;
  while (!is_scalar(cur)) { n++; cur = ld64(cur + 16); }
  u64 a = alloc_array(rt, n, n);
  cur = list;
  for (u64 i = 0; i < n; i++) {
    u64 v = ld64(cur + 8);
    inc_obj(v);
    st64(a + 24 + 8 * i, v);
    cur = ld64(cur + 16);
  }
  dec_obj(rt, list);
  return a;
}

u64 LCNF_FN(lcnf_array_to_list)(u64 rt, u64 arr) {
  u64 n = ld64(arr + 8);
  u64 list = 1ULL;
  u64 hdr = 1ULL | (24ULL << 32) | (2ULL << 48) | (1ULL << 56);
  for (u64 i = n; i-- > 0;) {
    u64 v = ld64(arr + 24 + 8 * i);
    inc_obj(v);
    u64 node = LCNF_FN(lcnf_alloc)(rt, 24);
    st64(node, hdr);
    st64(node + 8, v);
    st64(node + 16, list);
    list = node;
  }
  dec_obj(rt, arr);
  return list;
}

u64 LCNF_FN(lcnf_array_push)(u64 rt, u64 arr, u64 v) {
  u64 r = ensure_exclusive_array(rt, arr, 1);
  u64 sz = ld64(r + 8);
  st64(r + 24 + 8 * sz, v);
  st64(r + 8, sz + 1);
  return r;
}

u64 LCNF_FN(lcnf_array_replicate)(u64 rt, u64 n, u64 v) {
  if (!is_scalar(n)) lcnf_fatal("Array.replicate size too large");
  u64 cnt = unbox_nat(n);
  u64 a = alloc_array(rt, cnt, cnt);
  if (cnt == 0) {
    dec_obj(rt, v);
  } else {
    inc_obj_n(v, cnt - 1);
    for (u64 i = 0; i < cnt; i++) st64(a + 24 + 8 * i, v);
  }
  return a;
}

u64 LCNF_FN(lcnf_array_get)(u64 rt, u64 dv, u64 arr, u64 idx, u64 flags) {
  (void)rt;
  int borrowed = (flags & 1) != 0;
  int unboxed = (flags & 2) != 0;
  u64 sz = ld64(arr + 8);
  if (unboxed) {
    u64 v = ld64(arr + 24 + 8 * idx);
    if (!borrowed) inc_obj(v);
    return v;
  }
  if (is_scalar(idx)) {
    u64 i = unbox_nat(idx);
    if (i < sz) {
      u64 v = ld64(arr + 24 + 8 * i);
      if (!borrowed) inc_obj(v);
      return v;
    }
  }
  if (!borrowed) inc_obj(dv);
  return dv;
}

u64 LCNF_FN(lcnf_array_set)(u64 rt, u64 arr, u64 idx, u64 v, u64 unboxed) {
  u64 sz = ld64(arr + 8);
  u64 i = unboxed ? idx : (is_scalar(idx) ? unbox_nat(idx) : sz);
  if (i >= sz) {
    dec_obj(rt, v);
    return arr;
  }
  u64 r = ensure_exclusive_array(rt, arr, 0);
  u64 old = ld64(r + 24 + 8 * i);
  dec_obj(rt, old);
  st64(r + 24 + 8 * i, v);
  return r;
}

u64 LCNF_FN(lcnf_array_pop)(u64 rt, u64 arr) {
  u64 r = ensure_exclusive_array(rt, arr, 0);
  u64 sz = ld64(r + 8);
  if (sz == 0) return r;
  sz--;
  st64(r + 8, sz);
  dec_obj(rt, ld64(r + 24 + 8 * sz));
  return r;
}

u64 LCNF_FN(lcnf_array_swap)(u64 rt, u64 arr, u64 i, u64 j, u64 check_bounds) {
  u64 sz = ld64(arr + 8);
  if (check_bounds && (!is_scalar(i) || !is_scalar(j))) return arr;
  u64 ui = unbox_nat(i), uj = unbox_nat(j);
  if (check_bounds && (ui >= sz || uj >= sz)) return arr;
  u64 r = ensure_exclusive_array(rt, arr, 0);
  u64 a = ld64(r + 24 + 8 * ui), b = ld64(r + 24 + 8 * uj);
  st64(r + 24 + 8 * ui, b);
  st64(r + 24 + 8 * uj, a);
  return r;
}

/* ---- ByteArrays (ScalarArray, elem_size = 1) ---- */

static u64 alloc_sarray(u64 rt, u64 size, u64 cap) {
  u64 sz = (24 + cap + 7) & ~7ULL;
  u64 p = LCNF_FN(lcnf_alloc)(rt, sz);
  st64(p, 1ULL | (1ULL << 48) | ((u64)LCNF_SARRAY_TAG << 56));
  st64(p + 8, size);
  st64(p + 16, cap);
  return p;
}

static u64 ensure_exclusive_ba(u64 rt, u64 ba, int expand) {
  u64 sz = ld64(ba + 8), cap = ld64(ba + 16);
  if (is_excl(ba) && (!expand || sz < cap)) return ba;
  u64 new_cap = expand ? (cap == 0 ? 8 : (sz < cap ? cap : cap * 2)) : cap;
  u64 r = alloc_sarray(rt, sz, new_cap);
  mem_copy_bytes(r + 24, ba + 24, sz);
  dec_obj(rt, ba);
  return r;
}

u64 LCNF_FN(lcnf_ba_empty)(u64 rt) {
  LcnfState *s = lcnf_state(rt);
  if (!s->ba_empty) {
    u64 p = alloc_sarray(rt, 0, 0);
    LCNF_FN(lcnf_mark_persistent)(rt, p);
    s->ba_empty = p;
  }
  return s->ba_empty;
}

u64 LCNF_FN(lcnf_ba_mk_empty)(u64 rt, u64 cap) {
  u64 c = is_scalar(cap) ? unbox_nat(cap) : 0;
  return alloc_sarray(rt, 0, c);
}

u64 LCNF_FN(lcnf_ba_mk)(u64 rt, u64 arr) {
  u64 n = ld64(arr + 8);
  u64 ba = alloc_sarray(rt, n, n);
  for (u64 i = 0; i < n; i++) st8(ba + 24 + i, unbox_nat(ld64(arr + 24 + 8 * i)));
  dec_obj(rt, arr);
  return ba;
}

u64 LCNF_FN(lcnf_ba_data)(u64 rt, u64 ba) {
  u64 n = ld64(ba + 8);
  u64 arr = alloc_array(rt, n, n);
  for (u64 i = 0; i < n; i++) st64(arr + 24 + 8 * i, box_nat(ld8(ba + 24 + i)));
  dec_obj(rt, ba);
  return arr;
}

u64 LCNF_FN(lcnf_ba_push)(u64 rt, u64 ba, u64 b) {
  u64 r = ensure_exclusive_ba(rt, ba, 1);
  u64 sz = ld64(r + 8);
  st8(r + 24 + sz, b);
  st64(r + 8, sz + 1);
  return r;
}

u64 LCNF_FN(lcnf_ba_get)(u64 rt, u64 ba, u64 idx, u64 unboxed) {
  (void)rt;
  u64 sz = ld64(ba + 8);
  if (unboxed) return idx < sz ? ld8(ba + 24 + idx) : 0;
  if (!is_scalar(idx)) return 0;
  u64 i = unbox_nat(idx);
  return i < sz ? ld8(ba + 24 + i) : 0;
}

u64 LCNF_FN(lcnf_ba_set)(u64 rt, u64 ba, u64 idx, u64 b, u64 unboxed) {
  u64 sz = ld64(ba + 8);
  u64 i = unboxed ? idx : (is_scalar(idx) ? unbox_nat(idx) : sz);
  if (i >= sz) return ba;
  u64 r = ensure_exclusive_ba(rt, ba, 0);
  st8(r + 24 + i, b);
  return r;
}

u64 LCNF_FN(lcnf_ba_cmp_op)(u64 rt, u64 op, u64 a, u64 b) {
  (void)rt;
  if (a == b) return op == 0 ? 1 : (op == 1 ? 0 : 1);
  u64 la = ld64(a + 8), lb = ld64(b + 8);
  if (op == 0) {
    if (la != lb) return 0;
    return cmp_byte_slices(a + 24, la, b + 24, lb) == 0 ? 1 : 0;
  }
  int c = cmp_byte_slices(a + 24, la, b + 24, lb);
  if (op == 1) return c < 0 ? 1 : 0;
  return c < 0 ? 0 : (c == 0 ? 1 : 2);
}

/* ---- Float (IEEE 754 binary64 packed in u64) ---- */

static inline double u64_to_f64(u64 x) { double d; memcpy(&d, &x, 8); return d; }
static inline u64 f64_to_u64(double d) { u64 x; memcpy(&x, &d, 8); return x; }

u64 LCNF_FN(lcnf_float_bin)(u64 rt, u64 op, u64 a, u64 b) {
  (void)rt;
  double x = u64_to_f64(a), y = u64_to_f64(b);
  switch (op) {
    case 0: return f64_to_u64(x + y);
    case 1: return f64_to_u64(x - y);
    case 2: return f64_to_u64(x * y);
    case 3: return f64_to_u64(x / y);
    case 4: return x == y ? 1 : 0;
    case 5: return x < y ? 1 : 0;
    case 6: return x <= y ? 1 : 0;
    case 7: return f64_to_u64(pow(x, y));
    case 8: return f64_to_u64(atan2(x, y));
    case 9: return f64_to_u64(fmin(x, y));
    case 10: return f64_to_u64(fmax(x, y));
    default: return 0;
  }
}

u64 LCNF_FN(lcnf_float_un)(u64 rt, u64 op, u64 a) {
  double x = u64_to_f64(a);
  switch (op) {
    case 0: return f64_to_u64(-x);
    case 1: return f64_to_u64(fabs(x));
    case 2: return f64_to_u64(sqrt(x));
    case 3: return f64_to_u64(sin(x));
    case 4: return f64_to_u64(cos(x));
    case 5: return f64_to_u64(tan(x));
    case 6: return f64_to_u64(exp(x));
    case 7: return f64_to_u64(log(x));
    case 8: return f64_to_u64(floor(x));
    case 9: return f64_to_u64(ceil(x));
    case 10: return f64_to_u64(round(x));
    case 11: return isnan(x) ? 1 : 0;
    case 12: return isinf(x) ? 1 : 0;
    case 13: return isfinite(x) ? 1 : 0;
    case 14: return (x >= 0.0 && isfinite(x)) ? (uint64_t)x : 0ULL;
    case 15: return f64_to_u64((double)a);
    case 16: return (x >= 0.0 && isfinite(x)) ? (uint32_t)x : 0U;
    case 17: return (x >= 0.0 && isfinite(x)) ? (uint16_t)x : 0U;
    case 18: return (x >= 0.0 && isfinite(x)) ? (uint8_t)x : 0U;
    case 19: return isfinite(x) ? (u64)(int64_t)x : 0ULL;
    case 20: {
      char buf[64];
      int len = snprintf(buf, sizeof(buf), "%.17g", x);
      if (len < 0) len = 0;
      u64 s = LCNF_FN(lcnf_str_alloc)(rt, (u64)len, (u64)len);
      for (int i = 0; i < len; i++) st8(s + 32 + (u64)i, (uint8_t)buf[i]);
      return s;
    }
    default: return 0;
  }
}

u64 LCNF_FN(lcnf_float_of_sci)(u64 rt, u64 m, u64 neg, u64 e) {
  size_t mlen = 0;
  char *ms = nat_to_ascii(m, &mlen);
  u64 exp_v = is_scalar(e) ? unbox_nat(e) : 1000000ULL;
  dec_obj(rt, m);
  dec_obj(rt, e);
  size_t bsz = mlen + 32;
  char *buf = (char *)malloc(bsz);
  if (!buf) lcnf_fatal("float_of_sci out of memory");
  snprintf(buf, bsz, "%se%s%llu", ms, neg ? "-" : "", (unsigned long long)exp_v);
  free(ms);
  double d = strtod(buf, NULL);
  free(buf);
  return f64_to_u64(d);
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
