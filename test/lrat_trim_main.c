#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

extern void br_trim_proof(uintptr_t st);
extern void br_check_proof(uintptr_t st);
extern void br_check_clause(uintptr_t st, uintptr_t id, uintptr_t lits, uintptr_t ants);

static jmp_buf jb;
static uintptr_t fail_args[5];
static int failed;

_Noreturn void lrat_fail(uintptr_t c, uintptr_t a1, uintptr_t a2, uintptr_t a3, uintptr_t a4) {
  failed = 1;
  fail_args[0] = c;
  fail_args[1] = a1;
  fail_args[2] = a2;
  fail_args[3] = a3;
  fail_args[4] = a4;
  longjmp(jb, 1);
}

struct state_buf {
  uint64_t k[20];
  int32_t used[16];
  uint64_t ants_ptrs[16];
  uint64_t lits_ptrs[16];
  int8_t values_buf[16];
  int8_t marks_buf[16];
  int32_t trail[32];
  int32_t work[32];
};

static void init_base(struct state_buf *b, uint64_t strict, uint64_t trimming) {
  memset(b, 0, sizeof(*b));
  b->k[0] = (uintptr_t)b->used;
  b->k[1] = (uintptr_t)b->ants_ptrs;
  b->k[2] = (uintptr_t)b->lits_ptrs;
  b->k[3] = (uintptr_t)(b->values_buf + 8);
  b->k[4] = (uintptr_t)(b->marks_buf + 8);
  b->k[5] = (uintptr_t)b->trail;
  b->k[6] = (uintptr_t)b->trail;
  b->k[7] = (uintptr_t)b->work;
  b->k[8] = 9;
  b->k[9] = 6;
  b->k[10] = strict;
  b->k[11] = trimming;
  b->k[12] = 1;
  b->k[13] = 0;
}

int main(void) {
  static const int32_t c1[] = {1, 2, 0};
  static const int32_t c2[] = {1, -2, 0};
  static const int32_t c3[] = {-1, 2, 0};
  static const int32_t c4[] = {-1, -2, 0};
  static const int32_t c5[] = {1, 2, 0};
  static const int32_t c6[] = {1, 0};
  static const int32_t a6[] = {1, 2, 0};
  static const int32_t c7[] = {-2, 0};
  static const int32_t a7[] = {2, 4, 0};
  static const int32_t c8[] = {-1, 0};
  static const int32_t a8[] = {3, 4, 0};
  static const int32_t c9[] = {0};
  static const int32_t a9[] = {6, 8, 0};

  static const uint64_t exp_stats[4][6] = {
    {0, 0, 4, 1, 12, 7},
    {4, 3, 3, 1, 9, 5},
    {0, 0, 4, 1, 8, 0},
    {4, 3, 3, 1, 6, 0},
  };
  static const int32_t exp_used_trim[10] = {0, 6, 6, 8, 8, 0, 9, 0, 9, 9};

  struct state_buf b;
  int bad = 0;
  for (int strict = 0; strict <= 1; strict++) {
    for (int trim = 0; trim <= 1; trim++) {
      init_base(&b, strict, trim);
      b.lits_ptrs[1] = (uintptr_t)c1;
      b.lits_ptrs[2] = (uintptr_t)c2;
      b.lits_ptrs[3] = (uintptr_t)c3;
      b.lits_ptrs[4] = (uintptr_t)c4;
      b.lits_ptrs[5] = (uintptr_t)c5;
      b.lits_ptrs[6] = (uintptr_t)c6; b.ants_ptrs[6] = (uintptr_t)a6;
      b.lits_ptrs[7] = (uintptr_t)c7; b.ants_ptrs[7] = (uintptr_t)a7;
      b.lits_ptrs[8] = (uintptr_t)c8; b.ants_ptrs[8] = (uintptr_t)a8;
      b.lits_ptrs[9] = (uintptr_t)c9; b.ants_ptrs[9] = (uintptr_t)a9;
      failed = 0;
      if (setjmp(jb) == 0) {
        br_trim_proof((uintptr_t)b.k);
        br_check_proof((uintptr_t)b.k);
      }
      int idx = strict * 2 + trim;
      int ok = !failed && b.k[6] == b.k[5];
      for (int s = 0; s < 6; s++) ok &= (b.k[14 + s] == exp_stats[idx][s]);
      for (int i = 0; i < 10; i++) ok &= (b.used[i] == (trim ? exp_used_trim[i] : 0));
      printf("valid_strict%d_trim%d: %s\n", strict, trim, ok ? "ok" : "BAD");
      bad |= !ok;
    }
  }

  /* RUP failure: clause [1] from only antecedent [1] -> lrat_fail(3, 6, 0, 0, 0) */
  {
    static const int32_t bad_a6[] = {1, 0};
    init_base(&b, 0, 0);
    b.lits_ptrs[1] = (uintptr_t)c1;
    b.lits_ptrs[6] = (uintptr_t)c6; b.ants_ptrs[6] = (uintptr_t)bad_a6;
    b.k[8] = 6; b.k[9] = 6;
    failed = 0;
    if (setjmp(jb) == 0) br_check_proof((uintptr_t)b.k);
    int ok = failed && fail_args[0] == 3 && fail_args[1] == 6;
    printf("fail_rup: %s\n", ok ? "ok" : "BAD");
    bad |= !ok;
  }

  /* Strict failure codes 1, 3, 4, 5, 6, 7, 8 */
  static const int32_t ants_neg[] = {-1, 0};
  static const int32_t ants_empty[] = {0};
  static const int32_t ants_double_clash[] = {1, 4, 0};
  static const int32_t ants_no_clash[] = {6, 7, 0};
  static const int32_t lits_missing[] = {1, 2, 0};
  static const int32_t lits_wrong_sign[] = {-1, 0};
  static const int32_t lits_too_small[] = {0};

  struct { const char *name; const int32_t *lits; const int32_t *ants; uintptr_t code; int64_t a2; } sc[] = {
    {"strict_code1", c6, ants_neg, 1, -1},
    {"strict_code3", c6, ants_empty, 3, 0},
    {"strict_code4", c6, ants_double_clash, 4, 1},
    {"strict_code5", c6, ants_no_clash, 5, 6},
    {"strict_code6", lits_missing, a6, 6, 2},
    {"strict_code7", lits_wrong_sign, a6, 7, -1},
    {"strict_code8", lits_too_small, a6, 8, 1},
  };
  for (unsigned i = 0; i < sizeof(sc)/sizeof(sc[0]); i++) {
    init_base(&b, 1, 0);
    b.lits_ptrs[1] = (uintptr_t)c1;
    b.lits_ptrs[2] = (uintptr_t)c2;
    b.lits_ptrs[3] = (uintptr_t)c3;
    b.lits_ptrs[4] = (uintptr_t)c4;
    b.lits_ptrs[6] = (uintptr_t)c6;
    b.lits_ptrs[7] = (uintptr_t)c7;
    failed = 0;
    if (setjmp(jb) == 0) {
      br_check_clause((uintptr_t)b.k, 10 + i, (uintptr_t)sc[i].lits, (uintptr_t)sc[i].ants);
    }
    int ok = failed && fail_args[0] == sc[i].code && fail_args[1] == 10 + i &&
             (int64_t)fail_args[2] == sc[i].a2;
    printf("%s: %s\n", sc[i].name, ok ? "ok" : "BAD");
    bad |= !ok;
  }
  return bad;
}
