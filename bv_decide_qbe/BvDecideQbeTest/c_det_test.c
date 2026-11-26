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

extern uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                                   uint8_t *work_ptr, uint64_t work_cap,
                                   uint64_t fuel);
extern lean_obj_res leanqbe_alloc_work_buf(uint64_t n);
extern lean_obj_res leanqbe_solve_dimacs_bytes(b_lean_obj_arg cnf,
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

static unpacked_res_t run_shim(lean_object *cnf, lean_object *work, uint64_t fuel) {
  lean_obj_res r = leanqbe_solve_dimacs_bytes(cnf, work, fuel);
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

static void verify_4_mmap_determinism(const char *name,
                                      const char *cnf_str,
                                      size_t wsize,
                                      uint64_t fuel,
                                      unsigned expected_tag,
                                      size_t expected_mv) {
  static const uintptr_t kBases[4] = {
    0x510000000000ULL,
    0x560000000000ULL,
    0x610000000000ULL,
    0x660000000000ULL,
  };
  size_t cnf_len = strlen(cnf_str);
  uintptr_t seen_bases[4] = {0};
  unpacked_res_t ref = {0, 0, NULL};
  int have_ref = 0;

  for (int b = 0; b < 4; b++) {
    for (int run = 0; run < 2; run++) {
      guarded_sarray_t g_cnf = alloc_guarded_sarray_at(
          kBases[b] + 0x100000ULL, (const uint8_t *)cnf_str, cnf_len, 16, 0, 0);
      /* Use m_rc = 2 so lean_dec_ref(work) in shim drops rc to 1 without freeing mmap. */
      guarded_sarray_t g_work = alloc_guarded_sarray_at(
          kBases[b] + 0x400000ULL, NULL, wsize, 16, 1, 2);

      if (run == 0) {
        seen_bases[b] = (uintptr_t)g_work.base;
        for (int prev = 0; prev < b; prev++) {
          assert(seen_bases[b] != seen_bases[prev]);
        }
      }

      unpacked_res_t cur = run_shim(g_cnf.obj, g_work.obj, fuel);
      assert(cur.tag == expected_tag);
      if (expected_tag == 1) {
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
      free_guarded_sarray(g_cnf);
    }
  }

  /* Also verify leanqbe_alloc_work_buf + leanqbe_solve_dimacs_bytes matches bit-identically. */
  guarded_sarray_t g_cnf = alloc_guarded_sarray_at(
      0, (const uint8_t *)cnf_str, cnf_len, 16, 0, 0);
  lean_obj_res alloc_work = leanqbe_alloc_work_buf((uint64_t)wsize);
  unpacked_res_t alloc_res = run_shim(g_cnf.obj, alloc_work, fuel);
  assert(alloc_res.tag == ref.tag);
  assert(alloc_res.model_len == ref.model_len);
  if (alloc_res.model_len > 0) {
    assert(memcmp(alloc_res.model, ref.model, alloc_res.model_len) == 0);
  }
  free(alloc_res.model);
  free_guarded_sarray(g_cnf);

  free(ref.model);
  printf("  [OK] %-20s 4-mmap x 2 runs + allocWorkBuf bit-identical (tag=%u, mv=%zu)\n",
         name, expected_tag, expected_mv);
}

static void verify_direct_guarded_buf(const char *cnf_str, uint64_t expected_rc) {
  size_t cnf_len = strlen(cnf_str);
  size_t work_len = 262144;
  uint64_t rc_ref = 999;

  for (int i = 0; i < 4; i++) {
    guarded_buf_t cnf = alloc_guarded((const uint8_t *)cnf_str, cnf_len, 0);
    guarded_buf_t work = alloc_guarded(NULL, work_len, 1);
    uint64_t rc = kissat_solve_bytes(cnf.ptr, cnf.len, work.ptr, work.len, 100000000ULL);
    assert(rc == expected_rc);
    if (i == 0) rc_ref = rc;
    assert(rc == rc_ref);
    free_guarded(work);
    free_guarded(cnf);
  }
}

int main(void) {
  const char *unsat_2var =
      "p cnf 2 4\n"
      "1 2 0\n"
      "1 -2 0\n"
      "-1 2 0\n"
      "-1 -2 0\n";

  const char *unsat_php32 =
      "p cnf 6 9\n"
      "1 2 0\n"
      "3 4 0\n"
      "5 6 0\n"
      "-1 -3 0\n"
      "-1 -5 0\n"
      "-3 -5 0\n"
      "-2 -4 0\n"
      "-2 -6 0\n"
      "-4 -6 0\n";

  const char *sat_4var =
      "p cnf 4 5\n"
      "1 2 0\n"
      "-1 3 0\n"
      "-2 4 0\n"
      "-3 -4 1 0\n"
      "2 -4 0\n";

  const char *sat_8var =
      "p cnf 8 8\n"
      "1 2 0\n"
      "-2 3 0\n"
      "-3 4 0\n"
      "-4 5 0\n"
      "-5 6 0\n"
      "-6 7 0\n"
      "-7 8 0\n"
      "-8 -1 2 0\n";

  printf("== c_det_test: ASan/UBSan + 4-mmap determinism + guarded_buf.h ==\n");

  verify_4_mmap_determinism("unsat_2var", unsat_2var, 262144, 100000000ULL, 0, 0);
  verify_4_mmap_determinism("unsat_php32", unsat_php32, 262144, 100000000ULL, 0, 0);
  verify_4_mmap_determinism("sat_4var", sat_4var, 262144, 100000000ULL, 1, 4);
  verify_4_mmap_determinism("sat_8var", sat_8var, 262144, 100000000ULL, 1, 8);

  /* workTooSmall edge cases */
  verify_4_mmap_determinism("too_small_0", unsat_2var, 0, 100000000ULL, 3, 0);
  verify_4_mmap_determinism("too_small_3519", unsat_2var, 64 + 3455, 100000000ULL, 3, 0);
  verify_4_mmap_determinism("too_small_4096", unsat_php32, 4096, 100000000ULL, 3, 0);

  /* unknown on fuel = 1 */
  verify_4_mmap_determinism("unknown_fuel1", unsat_php32, 262144, 1ULL, 2, 0);

  /* Explicit COW test: rc = 2 alloc'd object -> shim must not mutate caller's buffer. */
  {
    size_t cnf_len = strlen(unsat_2var);
    guarded_sarray_t g_cnf = alloc_guarded_sarray_at(
        0, (const uint8_t *)unsat_2var, cnf_len, 16, 0, 0);
    lean_obj_res w = leanqbe_alloc_work_buf(262144);
    lean_inc_ref(w); /* rc becomes 2 */
    unpacked_res_t r = run_shim(g_cnf.obj, w, 100000000ULL);
    assert(r.tag == 0);
    assert(w->m_rc == 1);
    /* Caller's buffer must remain untouched (all zeroes) because !lean_is_exclusive. */
    uint8_t *p = lean_sarray_cptr(w);
    for (size_t i = 0; i < 128; i++) {
      assert(p[i] == 0);
    }
    lean_dec_ref(w);
    free_guarded_sarray(g_cnf);
    printf("  [OK] %-20s pure COW (rc=2) left shared work buffer untouched\n", "cow_shared");
  }

  /* Direct test/guarded_buf.h guard-page verification */
  verify_direct_guarded_buf(unsat_2var, 20ULL);
  verify_direct_guarded_buf(sat_4var, 10ULL);
  printf("  [OK] %-20s test/guarded_buf.h direct calls passed\n", "guarded_buf");

  printf("c_det_test: ALL PASSED\n");
  return 0;
}
