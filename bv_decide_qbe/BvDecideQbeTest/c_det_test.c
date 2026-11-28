#define _GNU_SOURCE
#include <assert.h>
#include <lean/lean.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

#include "../../test/guarded_buf.h"

extern uint64_t bv_solve_bytes(const uint8_t *prog_ptr, uint64_t prog_len,
                               uint8_t *work_ptr, uint64_t work_cap,
                               uint64_t fuel);
extern lean_obj_res leanqbe_alloc_work_buf(uint64_t n);
extern lean_obj_res leanqbe_solve_bv_bytes(b_lean_obj_arg prog,
                                             lean_obj_arg work,
                                             uint64_t fuel);

/* Minimal ASan-tracked Lean runtime stubs for standalone shim testing. */
void lean_notify_assert(const char *fileName, int line, const char *condition) {
  fprintf(stderr, "lean_notify_assert(%s:%d): %s\n",
          fileName ? fileName : "?", line, condition ? condition : "?");
  abort();
}

void lean_inc_heartbeat(void) {}

void lean_internal_panic(const char *msg) {
  fprintf(stderr, "lean_internal_panic: %s\n", msg ? msg : "(null)");
  abort();
}

void lean_internal_panic_overflow(void) {
  lean_internal_panic("overflow");
}

void lean_internal_panic_out_of_memory(void) {
  lean_internal_panic("out of memory");
}

lean_object *lean_alloc_object(size_t sz) {
  void *p = calloc(1, sz);
  if (!p) lean_internal_panic_out_of_memory();
  return (lean_object *)p;
}

lean_object *lean_alloc_small_object_core(unsigned sz) {
  void *p = calloc(1, sz);
  if (!p) lean_internal_panic_out_of_memory();
  lean_object *o = (lean_object *)p;
  o->m_cs_sz = sz;
  return o;
}

void *mi_malloc(size_t sz) {
  void *p = calloc(1, sz);
  if (!p) lean_internal_panic_out_of_memory();
  return p;
}

void mi_free(void *p) {
  free(p);
}

void lean_free_object(lean_object *o) {
  free(o);
}

void lean_dec_ref_cold(lean_object *o) {
  if (!o) return;
  if (o->m_rc == 1) {
    if (lean_is_ctor(o)) {
      unsigned n = lean_ctor_num_objs(o);
      for (unsigned i = 0; i < n; i++) {
        lean_dec(lean_ctor_get(o, i));
      }
    }
    lean_free_object(o);
  } else if (o->m_rc > 1) {
    o->m_rc--;
  }
}

typedef struct {
  void *base;
  size_t total;
  lean_object *obj;
} guarded_sarray_t;

static guarded_sarray_t alloc_guarded_sarray_at(uintptr_t hint_addr,
                                                const uint8_t *init,
                                                size_t len,
                                                size_t align_slack,
                                                int writable,
                                                int rc) {
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);
  size_t obj_sz = sizeof(lean_sarray_object) + len + align_slack;
  size_t data_pages = (obj_sz + pg - 1) / pg;
  size_t total = (data_pages + 2) * pg;

  void *hint = hint_addr ? (void *)hint_addr : NULL;
  uint8_t *base = (uint8_t *)mmap(hint, total, PROT_NONE,
                                  MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  assert(base != MAP_FAILED);

  uint8_t *mid = base + pg;
  int r = mprotect(mid, data_pages * pg, PROT_READ | PROT_WRITE);
  assert(r == 0);

  /* Place sarray so m_data + len ends right against the trailing guard page. */
  uintptr_t end_addr = (uintptr_t)(mid + data_pages * pg);
  uintptr_t obj_addr = (end_addr - sizeof(lean_sarray_object) - len) & ~(uintptr_t)7u;
  assert(obj_addr >= (uintptr_t)mid);

  lean_sarray_object *sa = (lean_sarray_object *)obj_addr;
  sa->m_header.m_rc = rc;
  sa->m_header.m_cs_sz = 0;
  sa->m_header.m_other = 1;
  sa->m_header.m_tag = LeanScalarArray;
  sa->m_size = len;
  sa->m_capacity = len;
  if (init && len > 0) {
    memcpy(sa->m_data, init, len);
  }

  if (!writable) {
    r = mprotect(mid, data_pages * pg, PROT_READ);
    assert(r == 0);
  }

  guarded_sarray_t gs = { base, total, (lean_object *)sa };
  return gs;
}

static void free_guarded_sarray(guarded_sarray_t gs) {
  int rc = munmap(gs.base, gs.total);
  assert(rc == 0);
}

typedef struct {
  unsigned tag;
  size_t model_len;
  uint8_t *model;
} unpacked_res_t;

static unpacked_res_t run_shim(lean_object *prog, lean_object *work, uint64_t fuel) {
  lean_obj_res r = leanqbe_solve_bv_bytes(prog, work, fuel);
  unpacked_res_t out = {0, 0, NULL};
  out.tag = lean_obj_tag(r);
  if (out.tag == 1) {
    lean_object *m = lean_ctor_get(r, 0);
    out.model_len = lean_sarray_size(m);
    if (out.model_len > 0) {
      out.model = (uint8_t *)malloc(out.model_len);
      assert(out.model != NULL);
      memcpy(out.model, lean_sarray_cptr(m), out.model_len);
    }
  }
  if (!lean_is_scalar(r)) {
    lean_dec_ref(r);
  }
  return out;
}

static size_t pack_words_le(uint8_t *dst, const uint32_t *ws, size_t nw) {
  for (size_t i = 0; i < nw; i++) {
    uint32_t w = ws[i];
    dst[4 * i + 0] = (uint8_t)(w & 0xFFu);
    dst[4 * i + 1] = (uint8_t)((w >> 8) & 0xFFu);
    dst[4 * i + 2] = (uint8_t)((w >> 16) & 0xFFu);
    dst[4 * i + 3] = (uint8_t)((w >> 24) & 0xFFu);
  }
  return nw * 4u;
}

static void verify_4_mmap_determinism(const char *name,
                                      const uint8_t *prog_bytes,
                                      size_t prog_len,
                                      size_t wsize,
                                      uint64_t fuel,
                                      unsigned expected_tag,
                                      int check_min_mv,
                                      size_t expected_mv) {
  static const uintptr_t kBases[4] = {
    0x510000000000ULL,
    0x560000000000ULL,
    0x610000000000ULL,
    0x660000000000ULL,
  };
  uintptr_t seen_bases[4] = {0};
  unpacked_res_t ref = {0, 0, NULL};
  int have_ref = 0;

  for (int b = 0; b < 4; b++) {
    for (int run = 0; run < 2; run++) {
      guarded_sarray_t g_prog = alloc_guarded_sarray_at(
          kBases[b] + 0x100000ULL, prog_bytes, prog_len, 16, 0, 0);
      /* Use m_rc = 2 so lean_dec_ref(work) in shim drops rc to 1 without freeing mmap. */
      guarded_sarray_t g_work = alloc_guarded_sarray_at(
          kBases[b] + 0x400000ULL, NULL, wsize, 16, 1, 2);

      if (run == 0) {
        seen_bases[b] = (uintptr_t)g_work.base;
        for (int prev = 0; prev < b; prev++) {
          assert(seen_bases[b] != seen_bases[prev]);
        }
      }

      unpacked_res_t cur = run_shim(g_prog.obj, g_work.obj, fuel);
      assert(cur.tag == expected_tag);
      if (expected_tag == 1 && check_min_mv) {
        assert(cur.model_len >= expected_mv);
      } else if (expected_tag == 1) {
        assert(cur.model_len == expected_mv);
      }

      if (!have_ref) {
        ref = cur;
        have_ref = 1;
      } else {
        assert(cur.tag == ref.tag);
        assert(cur.model_len == ref.model_len);
        if (cur.model_len > 0) {
          assert(memcmp(cur.model, ref.model, cur.model_len) == 0);
        }
        free(cur.model);
      }

      free_guarded_sarray(g_work);
      free_guarded_sarray(g_prog);
    }
  }

  /* Also verify leanqbe_alloc_work_buf + leanqbe_solve_bv_bytes matches bit-identically. */
  guarded_sarray_t g_prog = alloc_guarded_sarray_at(
      0, prog_bytes, prog_len, 16, 0, 0);
  lean_obj_res alloc_work = leanqbe_alloc_work_buf((uint64_t)wsize);
  unpacked_res_t alloc_res = run_shim(g_prog.obj, alloc_work, fuel);
  assert(alloc_res.tag == ref.tag);
  assert(alloc_res.model_len == ref.model_len);
  if (alloc_res.model_len > 0) {
    assert(memcmp(alloc_res.model, ref.model, alloc_res.model_len) == 0);
  }
  free(alloc_res.model);
  free_guarded_sarray(g_prog);

  free(ref.model);
  printf("  [OK] %-22s 4-mmap x 2 runs + allocWorkBuf bit-identical (tag=%u)\n",
         name, expected_tag);
}

static void verify_direct_guarded_buf(const uint8_t *prog_bytes, size_t prog_len,
                                      uint64_t expected_rc) {
  size_t work_len = 262144;
  for (int i = 0; i < 4; i++) {
    guarded_buf_t prog = alloc_guarded(prog_bytes, prog_len, 0);
    guarded_buf_t work = alloc_guarded(NULL, work_len, 1);
    uint64_t rc = bv_solve_bytes(prog.ptr, prog.len, work.ptr, work.len, 100000000ULL);
    assert(rc == expected_rc);
    free_guarded(work);
    free_guarded(prog);
  }
}

int main(void) {
  static const uint32_t w_triv_unsat[] = {
    0x31505642u, 1u, 0u, 1u, 0u, 0u, 0u, 0u,
    25u, 1u, 0u, 0u, 0u
  };
  static const uint32_t w_triv_sat[] = {
    0x31505642u, 1u, 0u, 1u, 0u, 0u, 0u, 0u,
    25u, 1u, 1u, 0u, 0u
  };
  static const uint32_t w_xor_self_unsat[] = {
    0x31505642u, 1u, 1u, 5u, 1u, 4u, 0u, 0u,
    0u, 2u,
    0u,
    0u, 2u, 0u, 0u, 0u,
    5u, 2u, 0u, 0u, 0u,
    1u, 2u, 0u, 0u, 0u,
    22u, 1u, 1u, 2u, 0u,
    26u, 1u, 3u, 0u, 0u
  };
  /* !( ((x & y) | (x & ~y)) == x ) on BitVec 8: requires Kissat CDCL (non-AIG-trivial) */
  static const uint32_t w_dist8_unsat[] = {
    0x31505642u, 1u, 2u, 8u, 0u, 7u, 0u, 0u,
    0u, 8u, 1u, 8u,
    0u, 8u, 0u, 0u, 0u,   /* 0: var 0 */
    0u, 8u, 1u, 0u, 0u,   /* 1: var 1 */
    3u, 8u, 0u, 1u, 0u,   /* 2: x & y */
    10u, 8u, 1u, 0u, 0u,  /* 3: ~y */
    3u, 8u, 0u, 3u, 0u,   /* 4: x & ~y */
    4u, 8u, 2u, 4u, 0u,   /* 5: (x & y) | (x & ~y) */
    22u, 1u, 5u, 0u, 0u,  /* 6: ... == x */
    26u, 1u, 6u, 0u, 0u   /* 7: !... */
  };
  static const uint32_t w_sat_add1[] = {
    0x31505642u, 1u, 1u, 5u, 2u, 4u, 0u, 0u,
    0u, 4u,
    1u, 0u,
    0u, 4u, 0u, 0u, 0u,
    1u, 4u, 0u, 0u, 0u,
    6u, 4u, 0u, 1u, 0u,
    1u, 4u, 1u, 0u, 0u,
    22u, 1u, 2u, 3u, 0u
  };
  static const uint32_t w_bad_magic[] = {
    0xDEADBEEFu, 1u, 0u, 1u, 0u, 0u, 0u, 0u,
    25u, 1u, 0u, 0u, 0u
  };
  static const uint32_t w_bad_opcode[] = {
    0x31505642u, 1u, 0u, 1u, 0u, 0u, 0u, 0u,
    999u, 1u, 0u, 0u, 0u
  };

  uint8_t p_triv_unsat[sizeof(w_triv_unsat)];
  uint8_t p_triv_sat[sizeof(w_triv_sat)];
  uint8_t p_xor_self[sizeof(w_xor_self_unsat)];
  uint8_t p_dist8[sizeof(w_dist8_unsat)];
  uint8_t p_sat_add1[sizeof(w_sat_add1)];
  uint8_t p_bad_magic[sizeof(w_bad_magic)];
  uint8_t p_bad_opcode[sizeof(w_bad_opcode)];

  size_t l_triv_unsat = pack_words_le(p_triv_unsat, w_triv_unsat, sizeof(w_triv_unsat) / 4u);
  size_t l_triv_sat = pack_words_le(p_triv_sat, w_triv_sat, sizeof(w_triv_sat) / 4u);
  size_t l_xor_self = pack_words_le(p_xor_self, w_xor_self_unsat, sizeof(w_xor_self_unsat) / 4u);
  size_t l_dist8 = pack_words_le(p_dist8, w_dist8_unsat, sizeof(w_dist8_unsat) / 4u);
  size_t l_sat_add1 = pack_words_le(p_sat_add1, w_sat_add1, sizeof(w_sat_add1) / 4u);
  size_t l_bad_magic = pack_words_le(p_bad_magic, w_bad_magic, sizeof(w_bad_magic) / 4u);
  size_t l_bad_opcode = pack_words_le(p_bad_opcode, w_bad_opcode, sizeof(w_bad_opcode) / 4u);

  printf("== c_det_test: ASan/UBSan + 4-mmap determinism + bv_solve_bytes ==\n");

  verify_4_mmap_determinism("bv_triv_unsat", p_triv_unsat, l_triv_unsat,
                            262144, 100000000ULL, 0, 0, 0);
  verify_4_mmap_determinism("bv_triv_sat", p_triv_sat, l_triv_sat, 262144, 100000000ULL, 1, 0, 0);
  verify_4_mmap_determinism("bv_xor_self_unsat", p_xor_self, l_xor_self,
                            262144, 100000000ULL, 0, 0, 0);
  verify_4_mmap_determinism("bv_dist8_unsat", p_dist8, l_dist8, 262144, 100000000ULL, 0, 0, 0);
  verify_4_mmap_determinism("bv_sat_add1", p_sat_add1, l_sat_add1, 262144, 100000000ULL, 1, 1, 5);

  /* Verify decoded SAT model for (x + 1#4 == 0#4) sets bits 1..4 = 1 (x = 15). */
  {
    guarded_sarray_t g_prog = alloc_guarded_sarray_at(0, p_sat_add1, l_sat_add1, 16, 0, 0);
    lean_obj_res w = leanqbe_alloc_work_buf(262144);
    unpacked_res_t r = run_shim(g_prog.obj, w, 100000000ULL);
    assert(r.tag == 1);
    assert(r.model_len >= 5);
    for (int j = 0; j < 4; j++) {
      assert(r.model[1 + j] == 1);
    }
    free(r.model);
    free_guarded_sarray(g_prog);
    printf("  [OK] %-22s x + 1#4 == 0#4 decoded x = 15#4\n", "bv_sat_add1_val");
  }

  /* workTooSmall edge cases (including M6Hdr 3456B header & tight Kissat arena/watch-stack OOMs) */
  verify_4_mmap_determinism("too_small_0", p_dist8, l_dist8, 0, 100000000ULL, 3, 0, 0);
  verify_4_mmap_determinism("too_small_3519", p_dist8, l_dist8, 64 + 3455, 100000000ULL, 3, 0, 0);
  verify_4_mmap_determinism("too_small_4096", p_dist8, l_dist8, 4096, 100000000ULL, 3, 0, 0);
  verify_4_mmap_determinism("too_small_8192", p_dist8, l_dist8, 8192, 100000000ULL, 3, 0, 0);

  /* Regression check: tight 8-bit mul OOM escalates via tag 3 -> tag 0 without .unknown. */
  {
    static const uint32_t w_tight_mul8[] = {
      0x31505642u, 1u, 2u, 6u, 0u, 5u, 0u, 0u,
      0u, 8u, 1u, 8u,
      0u, 8u, 0u, 0u, 0u,
      0u, 8u, 1u, 0u, 0u,
      7u, 8u, 0u, 1u, 0u,
      7u, 8u, 1u, 0u, 0u,
      22u, 1u, 2u, 3u, 0u,
      26u, 1u, 4u, 0u, 0u
    };
    uint8_t p_tight_mul8[sizeof(w_tight_mul8)];
    size_t l_tight_mul8 = pack_words_le(p_tight_mul8, w_tight_mul8, sizeof(w_tight_mul8) / 4u);
    guarded_sarray_t g_prog = alloc_guarded_sarray_at(0, p_tight_mul8, l_tight_mul8, 16, 0, 0);
    size_t ws = 16384;
    while (ws <= 4194304) {
      lean_obj_res w = leanqbe_alloc_work_buf((uint64_t)ws);
      unpacked_res_t r = run_shim(g_prog.obj, w, 100000000ULL);
      assert(r.tag == 3 || r.tag == 0);
      if (r.tag == 0) {
        break;
      }
      ws *= 2;
    }
    assert(ws <= 4194304);
    free_guarded_sarray(g_prog);
    printf("  [OK] %-22s tight 8-bit mul retry converged at %zu B without .unknown\n",
           "tight_mul8_oom", ws);
  }

  /* timeout (tag 4) on fuel = 0 and fuel = 1; unknown (tag 2) on invalid BVP1 */
  verify_4_mmap_determinism("timeout_fuel0", p_dist8, l_dist8, 262144, 0ULL, 4, 0, 0);
  verify_4_mmap_determinism("timeout_fuel1", p_dist8, l_dist8, 262144, 1ULL, 4, 0, 0);
  verify_4_mmap_determinism("invalid_magic", p_bad_magic, l_bad_magic,
                            262144, 100000000ULL, 2, 0, 0);
  verify_4_mmap_determinism("invalid_opcode", p_bad_opcode, l_bad_opcode,
                            262144, 100000000ULL, 2, 0, 0);

  /* Explicit COW test (rc = 2 -> untouched) & dirty exclusive buffer clearing test (rc = 1). */
  {
    guarded_sarray_t g_prog = alloc_guarded_sarray_at(0, p_dist8, l_dist8, 16, 0, 0);
    lean_obj_res w = leanqbe_alloc_work_buf(262144);
    memset(lean_sarray_cptr(w), 0xA5, 262144);
    lean_inc_ref(w); /* rc becomes 2 */
    unpacked_res_t r = run_shim(g_prog.obj, w, 100000000ULL);
    assert(r.tag == 0);
    assert(w->m_rc == 1);
    uint8_t *p = lean_sarray_cptr(w);
    for (size_t i = 0; i < 128; i++) {
      assert(p[i] == 0xA5);
    }
    /* Reuse dirty buffer (rc = 1) with fuel = 1 -> clears M6Hdr & returns timeout (4). */
    unpacked_res_t r2 = run_shim(g_prog.obj, w, 1ULL);
    assert(r2.tag == 4);
    free_guarded_sarray(g_prog);
    printf("  [OK] %-22s COW (rc=2) untouched & exclusive dirty reuse (rc=1) clean\n",
           "cow_and_reuse");
  }

  /* Direct dirty-workspace determinism check across 0x00 / 0xA5 / 0xFF fills (lazy alloc). */
  {
    static const uint8_t kFills[3] = { 0x00u, 0xA5u, 0xFFu };
    struct {
      const char *name;
      const uint8_t *prog;
      size_t len;
      unsigned tag;
    } cases[] = {
      { "bv_triv_unsat", p_triv_unsat, l_triv_unsat, 0u },
      { "bv_triv_sat", p_triv_sat, l_triv_sat, 1u },
      { "bv_xor_self_unsat", p_xor_self, l_xor_self, 0u },
      { "bv_dist8_unsat", p_dist8, l_dist8, 0u },
      { "bv_sat_add1", p_sat_add1, l_sat_add1, 1u },
    };
    for (size_t c = 0; c < sizeof(cases) / sizeof(cases[0]); c++) {
      unpacked_res_t base_r = {0, 0, NULL};
      for (int f = 0; f < 3; f++) {
        guarded_sarray_t g_prog = alloc_guarded_sarray_at(
            0, cases[c].prog, cases[c].len, 16, 0, 0);
        lean_obj_res w = leanqbe_alloc_work_buf(262144);
        memset(lean_sarray_cptr(w), kFills[f], 262144);
        unpacked_res_t cur = run_shim(g_prog.obj, w, 100000000ULL);
        assert(cur.tag == cases[c].tag);
        if (f == 0) {
          base_r = cur;
        } else {
          assert(cur.tag == base_r.tag);
          assert(cur.model_len == base_r.model_len);
          if (cur.model_len > 0) {
            assert(memcmp(cur.model, base_r.model, cur.model_len) == 0);
          }
          free(cur.model);
        }
        free_guarded_sarray(g_prog);
      }
      free(base_r.model);
    }
    printf("  [OK] %-22s 0x00/0xA5/0xFF dirty-buffer determinism bit-identical\n",
           "dirty_fill_det");
  }

  /* Direct test/guarded_buf.h guard-page verification on bv_solve_bytes */
  verify_direct_guarded_buf(p_triv_unsat, l_triv_unsat, 20ULL);
  verify_direct_guarded_buf(p_dist8, l_dist8, 20ULL);
  verify_direct_guarded_buf(p_sat_add1, l_sat_add1, 10ULL);
  printf("  [OK] %-22s test/guarded_buf.h direct bv_solve_bytes calls passed\n", "guarded_buf");

  printf("c_det_test: ALL PASSED\n");
  return 0;
}
