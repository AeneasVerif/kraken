#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

extern uint64_t lrat_check_bytes(
    const uint8_t *cnf_ptr, uint64_t cnf_len,
    const uint8_t *prf_ptr, uint64_t prf_len,
    uint8_t *work_ptr, uint64_t work_len);

typedef struct {
  void *base;
  size_t total;
  uint8_t *ptr;
  size_t len;
} guarded_buf_t;

static guarded_buf_t alloc_guarded(const uint8_t *init, size_t len, int writable) {
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);
  size_t data_pages = ((len == 0 ? 1 : len) + pg - 1) / pg;
  size_t total = (data_pages + 2) * pg;
  uint8_t *base = mmap(NULL, total, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  assert(base != MAP_FAILED);
  uint8_t *mid = base + pg;
  int rc = mprotect(mid, data_pages * pg, PROT_READ | PROT_WRITE);
  assert(rc == 0);
  memset(mid, 0xAA, data_pages * pg);
  /* Place buffer right up against the trailing PROT_NONE guard page! */
  uint8_t *ptr = mid + data_pages * pg - len;
  if (init && len > 0) {
    memcpy(ptr, init, len);
  }
  if (!writable) {
    rc = mprotect(mid, data_pages * pg, PROT_READ);
    assert(rc == 0);
  }
  guarded_buf_t g = { base, total, ptr, len };
  return g;
}

static void free_guarded(guarded_buf_t g) {
  int rc = munmap(g.base, g.total);
  assert(rc == 0);
}

static void run_case(
    const char *label,
    const uint8_t *cnf, size_t cnf_len,
    const uint8_t *prf, size_t prf_len,
    size_t work_len, uint64_t expected) {
  guarded_buf_t gc = alloc_guarded(cnf, cnf_len, 0);
  guarded_buf_t gp = alloc_guarded(prf, prf_len, 0);
  guarded_buf_t gw = alloc_guarded(NULL, work_len, 1);

  /* Check prefix poison before work_ptr stays untouched. */
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);
  uint8_t *w_mid = (uint8_t *)gw.base + pg;
  uint64_t got = lrat_check_bytes(gc.ptr, cnf_len, gp.ptr, prf_len, gw.ptr, work_len);
  if (got != expected) {
    fprintf(stderr, "FAIL %s: expected %llu, got %llu\n",
            label, (unsigned long long)expected, (unsigned long long)got);
    exit(1);
  }
  for (uint8_t *p = w_mid; p < gw.ptr; p++) {
    if (*p != 0xAA) {
      fprintf(stderr, "FAIL %s: wrote before work_ptr!\n", label);
      exit(1);
    }
  }

  free_guarded(gw);
  free_guarded(gp);
  free_guarded(gc);
}

static size_t put_leb(uint8_t *out, uint64_t n) {
  size_t k = 0;
  do {
    uint8_t b = (uint8_t)(n & 0x7f);
    n >>= 7;
    if (n != 0) b |= 0x80;
    out[k++] = b;
  } while (n != 0);
  return k;
}

static size_t put_lit(uint8_t *out, int32_t lit) {
  if (lit == 0) {
    out[0] = 0;
    return 1;
  }
  uint64_t v = lit > 0 ? (uint64_t)lit : (uint64_t)(-(int64_t)lit);
  uint64_t u = (v << 1) | (lit < 0 ? 1u : 0u);
  return put_leb(out, u);
}

int main(void) {
  /* 1. Exact nvDimacsBytes + nvLratAcceptBytes ('a' + 'd' + 'a' []) -> 1 */
  {
    const char *cnf = "p cnf 1 2\n1 0\n-1 0\n";
    uint8_t prf[64];
    size_t n = 0;
    /* 'a' id=3 lits=[1] hints=[1] */
    prf[n++] = 'a'; n += put_leb(prf + n, 6); n += put_lit(prf + n, 1); prf[n++] = 0;
    n += put_leb(prf + n, 2); prf[n++] = 0;
    /* 'd' ids=[1] */
    prf[n++] = 'd'; n += put_leb(prf + n, 2); prf[n++] = 0;
    /* 'a' id=4 lits=[] hints=[3, 2] */
    prf[n++] = 'a'; n += put_leb(prf + n, 8); prf[n++] = 0;
    n += put_leb(prf + n, 6); n += put_leb(prf + n, 4); prf[n++] = 0;
    run_case("nv_accept", (const uint8_t *)cnf, strlen(cnf), prf, n, 512, 1);
  }

  /* 2. Exact nvDimacsBytes + nvLratRejectBytes (non-conflict) -> 0 */
  {
    const char *cnf = "p cnf 1 2\n1 0\n-1 0\n";
    uint8_t prf[32];
    size_t n = 0;
    prf[n++] = 'a'; n += put_leb(prf + n, 6); prf[n++] = 0;
    n += put_leb(prf + n, 2); prf[n++] = 0;
    run_case("nv_reject", (const uint8_t *)cnf, strlen(cnf), prf, n, 512, 0);
  }

  /* 3. Comments, CRLF, tabs, 2-variable 4-clause UNSAT formula -> 1 */
  {
    const char *cnf =
        "c leading comment\r\n"
        "c another comment\n"
        "  p \t cnf  2   4 \r\n"
        "1 2 0 c inline-ish comment after zero\n"
        "-1 2 0\n"
        "1 -2 0\n"
        "-1 -2 0\n"
        "c trailing comment without newline";
    uint8_t prf[128];
    size_t n = 0;
    /* 5: [2] from [1, 2] */
    prf[n++] = 'a'; n += put_leb(prf + n, 10); n += put_lit(prf + n, 2); prf[n++] = 0;
    n += put_leb(prf + n, 2); n += put_leb(prf + n, 4); prf[n++] = 0;
    /* d [1, 2] */
    prf[n++] = 'd'; n += put_leb(prf + n, 2); n += put_leb(prf + n, 4); prf[n++] = 0;
    /* 6: [-2] from [3, 4] */
    prf[n++] = 'a'; n += put_leb(prf + n, 12); n += put_lit(prf + n, -2); prf[n++] = 0;
    n += put_leb(prf + n, 6); n += put_leb(prf + n, 8); prf[n++] = 0;
    /* 7: [] from [5, 6] */
    prf[n++] = 'a'; n += put_leb(prf + n, 14); prf[n++] = 0;
    n += put_leb(prf + n, 10); n += put_leb(prf + n, 12); prf[n++] = 0;
    run_case("2var_unsat_comments", (const uint8_t *)cnf, strlen(cnf), prf, n, 2048, 1);

    /* Same valid inputs but too small work buffers -> must cleanly return 0 without OOB! */
    run_case("work_0", (const uint8_t *)cnf, strlen(cnf), prf, n, 0, 0);
    run_case("work_64", (const uint8_t *)cnf, strlen(cnf), prf, n, 64, 0);
    run_case("work_127", (const uint8_t *)cnf, strlen(cnf), prf, n, 127, 0);
    run_case("work_128", (const uint8_t *)cnf, strlen(cnf), prf, n, 128, 0);
    run_case("work_160", (const uint8_t *)cnf, strlen(cnf), prf, n, 160, 0);
  }

  /* 4. Tautology addition step ('a' id=3 [1, -1] []) followed by [] -> 1 */
  {
    const char *cnf = "p cnf 1 2\n1 0\n-1 0\n";
    uint8_t prf[64];
    size_t n = 0;
    prf[n++] = 'a'; n += put_leb(prf + n, 6);
    n += put_lit(prf + n, 1); n += put_lit(prf + n, -1); prf[n++] = 0;
    prf[n++] = 0;
    prf[n++] = 'a'; n += put_leb(prf + n, 8); prf[n++] = 0;
    n += put_leb(prf + n, 2); n += put_leb(prf + n, 4); prf[n++] = 0;
    run_case("tautology_step", (const uint8_t *)cnf, strlen(cnf), prf, n, 1024, 1);
  }

  /* 5. Malformed DIMACS cases -> all 0 */
  {
    uint8_t prf[8] = { 'a', 4, 0, 2, 0 };
    const char *bad_dimacs[] = {
      "",
      "p cnf 1\n",
      "p cnf 1 1\n-0 0\n",
      "p cnf 1 1\n2 0\n",
      "p cnf 1 2\n1 0\n",
      "p cnf 1 1\n1 0\n-1 0\n",
      "p cnf 1 1\n0\nextra\n",
      "p cnf 268435456 1\n0\n",
      "p cnf 1 1\n1",
    };
    for (size_t i = 0; i < sizeof(bad_dimacs) / sizeof(bad_dimacs[0]); i++) {
      char lbl[32];
      snprintf(lbl, sizeof(lbl), "bad_dimacs_%zu", i);
      run_case(lbl, (const uint8_t *)bad_dimacs[i], strlen(bad_dimacs[i]), prf, 5, 1024, 0);
    }
  }

  /* 6. Malformed Binary LRAT cases -> all 0 */
  {
    const char *cnf = "p cnf 1 2\n1 0\n-1 0\n";
    /* Empty proof (EOF before deriving []) */
    run_case("prf_empty", (const uint8_t *)cnf, strlen(cnf), (const uint8_t *)"", 0, 1024, 0);
    /* Unknown tag */
    const uint8_t bad_tag[] = { 'x', 6, 0, 2, 4, 0 };
    run_case("prf_bad_tag", (const uint8_t *)cnf, strlen(cnf), bad_tag, sizeof(bad_tag), 1024, 0);
    /* Odd clause ID (u = 7) */
    const uint8_t odd_id[] = { 'a', 7, 0, 2, 4, 0 };
    run_case("prf_odd_id", (const uint8_t *)cnf, strlen(cnf), odd_id, sizeof(odd_id), 1024, 0);
    /* Clause ID <= nc (id = 2 -> u = 4) */
    const uint8_t dup_nc[] = { 'a', 4, 0, 2, 4, 0 };
    run_case("prf_id_le_nc", (const uint8_t *)cnf, strlen(cnf), dup_nc, sizeof(dup_nc), 1024, 0);
    /* Negative zero literal (u = 1) */
    const uint8_t neg_zero[] = { 'a', 6, 1, 0, 2, 4, 0 };
    run_case("prf_neg_zero_lit", (const uint8_t *)cnf, strlen(cnf), neg_zero, sizeof(neg_zero), 1024, 0);
    /* Out-of-range variable in literal (var 2 -> u = 4 when mv = 1) */
    const uint8_t oob_var[] = { 'a', 6, 4, 0, 2, 4, 0 };
    run_case("prf_oob_var", (const uint8_t *)cnf, strlen(cnf), oob_var, sizeof(oob_var), 1024, 0);
    /* 5-byte LEB128 rejected */
    const uint8_t leb5[] = { 'a', 0x86, 0x80, 0x80, 0x80, 0x00, 0, 2, 4, 0 };
    run_case("prf_leb5", (const uint8_t *)cnf, strlen(cnf), leb5, sizeof(leb5), 1024, 0);
    /* Using deleted clause ID 1 after 'd' [1] */
    const uint8_t use_del[] = { 'd', 2, 0, 'a', 6, 0, 2, 4, 0 };
    run_case("prf_use_deleted", (const uint8_t *)cnf, strlen(cnf), use_del, sizeof(use_del), 1024, 0);
    /* Deleting already deleted clause ID 1 twice */
    const uint8_t dbl_del[] = { 'd', 2, 2, 0, 'a', 6, 0, 4, 0 };
    run_case("prf_double_delete", (const uint8_t *)cnf, strlen(cnf), dbl_del, sizeof(dbl_del), 1024, 0);
  }

  return 0;
}
