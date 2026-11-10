#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

typedef uintptr_t br_word_t;

_Noreturn void lrat_fail(uintptr_t code, uintptr_t id, uintptr_t a, uintptr_t x,
                         uintptr_t y) {
  fprintf(stderr, "FAIL: lrat_fail(code=%" PRIuPTR ", id=%" PRIuPTR
                  ", a=%" PRIuPTR ", x=%" PRIuPTR ", y=%" PRIuPTR ")\n",
          code, id, a, x, y);
  exit(1);
}

/* Matches `KernelFields` in `Kraken/Bedrock2/Test/LratTrimSpec.lean` (20 words = 160 bytes). */
struct lrat_kernel_state {
  uint64_t used_begin;        /* 0 */
  uint64_t antecedents_begin; /* 8 */
  uint64_t literals_begin;    /* 16 */
  uint64_t values_begin;      /* 24 */
  uint64_t marks_begin;       /* 32 */
  uint64_t trail_begin;       /* 40 */
  uint64_t trail_end;         /* 48 */
  uint64_t work_begin;        /* 56 */
  uint64_t empty_clause;      /* 64 */
  uint64_t first_proof_id;    /* 72 */
  uint64_t strict;            /* 80 */
  uint64_t trimming;          /* 88 */
  uint64_t checking;          /* 96 */
  uint64_t forward;           /* 104 */
  uint64_t stat_trimmed_cnf;  /* 112 */
  uint64_t stat_trimmed_prf;  /* 120 */
  uint64_t stat_chk_total;    /* 128 */
  uint64_t stat_chk_empty;    /* 136 */
  uint64_t stat_resolved;     /* 144 */
  uint64_t stat_lit_assigned; /* 152 */
};

extern void br_trim_proof(br_word_t st);
extern void br_check_proof(br_word_t st);
extern void br_check_clause(br_word_t st, br_word_t id, br_word_t literals,
                            br_word_t antecedents);
extern void br_check_clause_non_strictly_by_propagation(br_word_t st,
                                                        br_word_t id,
                                                        br_word_t literals,
                                                        br_word_t antecedents);

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1e6;
}

/*
 * Builds a synthetic LRAT instance with M steps that is simultaneously valid for:
 *   - `br_trim_proof` (with unused CNF and proof clauses to exercise trimming),
 *   - `br_check_proof` with `strict = 0` (RUP unit propagation), and
 *   - `br_check_proof` with `strict = 1` (strict backward resolution).
 *
 * Variables: 1 .. 5 + M
 * Original CNF clauses (1 .. 6 + M):
 *   1..4: unit clauses [1, 0], [2, 0], [3, 0], [4, 0]
 *   5:    unit clause  [5, 0]
 *   5 + s (1 <= s <= M): [-1, -2, -3, -4, -(4 + s), 5 + s, 0]
 *   6 + M:               [-1, -2, -3, -4, -(5 + M), 0]
 *   7 + M:               [1, 2, 0] (unused original clause, trimmed away)
 *
 * First proof ID = 8 + M.
 * Proof clauses:
 *   For s = 1 .. M, clause id = 7 + M + s:
 *     literals:    [5 + s, 0]
 *     antecedents: [1, 2, 3, 4, (s == 1 ? 5 : 6 + M + s), 5 + s, 0]
 *   Unused proof clause id = 8 + 2*M:
 *     literals:    [1, 0], antecedents: [1, 0] (trimmed away when trimming=1)
 *   Empty clause id = 9 + 2*M:
 *     literals:    [0]
 *     antecedents: [1, 2, 3, 4, 7 + 2*M, 6 + M, 0]
 */
int main(int argc, char **argv) {
  int rup_only = (argc > 1 && strcmp(argv[1], "rup") == 0);
  const int M = 2000;
  const int ROUNDS = 150;
  const int max_var = 5 + M + 2;
  const int first_proof_id = 8 + M;
  const int empty_id = 9 + 2 * M;
  const int max_id = empty_id + 2;

  int32_t *used = (int32_t *)calloc((size_t)max_id, sizeof(int32_t));
  int32_t **ants = (int32_t **)calloc((size_t)max_id, sizeof(int32_t *));
  int32_t **lits = (int32_t **)calloc((size_t)max_id, sizeof(int32_t *));
  int8_t *values_buf = (int8_t *)calloc((size_t)(max_var * 2 + 16), 1);
  int8_t *marks_buf = (int8_t *)calloc((size_t)(max_var * 2 + 16), 1);
  int32_t *trail = (int32_t *)calloc((size_t)(max_var + 16), sizeof(int32_t));
  int32_t *work = (int32_t *)calloc((size_t)(max_id + 16), sizeof(int32_t));
  int32_t *pool = (int32_t *)calloc((size_t)(max_id * 16), sizeof(int32_t));
  size_t pool_pos = 0;

  for (int i = 1; i <= 5; i++) {
    int32_t *c = &pool[pool_pos];
    pool_pos += 2;
    c[0] = i;
    c[1] = 0;
    lits[i] = c;
  }
  for (int s = 1; s <= M; s++) {
    int id = 5 + s;
    int32_t *c = &pool[pool_pos];
    pool_pos += 7;
    c[0] = -1;
    c[1] = -2;
    c[2] = -3;
    c[3] = -4;
    c[4] = -(4 + s);
    c[5] = 5 + s;
    c[6] = 0;
    lits[id] = c;
  }
  {
    int id = 6 + M;
    int32_t *c = &pool[pool_pos];
    pool_pos += 6;
    c[0] = -1;
    c[1] = -2;
    c[2] = -3;
    c[3] = -4;
    c[4] = -(5 + M);
    c[5] = 0;
    lits[id] = c;
  }
  {
    int id = 7 + M;
    int32_t *c = &pool[pool_pos];
    pool_pos += 3;
    c[0] = 1;
    c[1] = 2;
    c[2] = 0;
    lits[id] = c;
  }
  for (int s = 1; s <= M; s++) {
    int id = 7 + M + s;
    int32_t *c = &pool[pool_pos];
    pool_pos += 2;
    c[0] = 5 + s;
    c[1] = 0;
    lits[id] = c;

    int32_t *a = &pool[pool_pos];
    pool_pos += 7;
    a[0] = 1;
    a[1] = 2;
    a[2] = 3;
    a[3] = 4;
    a[4] = (s == 1) ? 5 : (6 + M + s);
    a[5] = 5 + s;
    a[6] = 0;
    ants[id] = a;
  }
  {
    int id = 8 + 2 * M;
    int32_t *c = &pool[pool_pos];
    pool_pos += 2;
    c[0] = 1;
    c[1] = 0;
    lits[id] = c;
    int32_t *a = &pool[pool_pos];
    pool_pos += 2;
    a[0] = 1;
    a[1] = 0;
    ants[id] = a;
  }
  {
    int32_t *c = &pool[pool_pos];
    pool_pos += 1;
    c[0] = 0;
    lits[empty_id] = c;
    int32_t *a = &pool[pool_pos];
    pool_pos += 7;
    a[0] = 1;
    a[1] = 2;
    a[2] = 3;
    a[3] = 4;
    a[4] = 7 + 2 * M;
    a[5] = 6 + M;
    a[6] = 0;
    ants[empty_id] = a;
  }

  struct lrat_kernel_state st;
  memset(&st, 0, sizeof(st));
  st.used_begin = (uint64_t)(uintptr_t)used;
  st.antecedents_begin = (uint64_t)(uintptr_t)ants;
  st.literals_begin = (uint64_t)(uintptr_t)lits;
  st.values_begin = (uint64_t)(uintptr_t)values_buf;
  st.marks_begin = (uint64_t)(uintptr_t)marks_buf;
  st.trail_begin = (uint64_t)(uintptr_t)trail;
  st.trail_end = (uint64_t)(uintptr_t)trail;
  st.work_begin = (uint64_t)(uintptr_t)work;
  st.empty_clause = (uint64_t)empty_id;
  st.first_proof_id = (uint64_t)first_proof_id;
  st.trimming = 1;
  st.checking = 1;
  st.forward = 0;

  double t0 = now_ms();
  for (int r = 0; r < ROUNDS; r++) {
    if (rup_only) {
      for (int s = 1; s <= M; s++) {
        int id = 7 + M + s;
        br_check_clause_non_strictly_by_propagation(
            (br_word_t)(uintptr_t)&st, (br_word_t)id,
            (br_word_t)(uintptr_t)lits[id], (br_word_t)(uintptr_t)ants[id]);
      }
      br_check_clause_non_strictly_by_propagation(
          (br_word_t)(uintptr_t)&st, (br_word_t)empty_id,
          (br_word_t)(uintptr_t)lits[empty_id],
          (br_word_t)(uintptr_t)ants[empty_id]);
    } else {
      memset(used, 0, (size_t)max_id * sizeof(int32_t));
      br_trim_proof((br_word_t)(uintptr_t)&st);
      st.strict = 0;
      br_check_proof((br_word_t)(uintptr_t)&st);
      st.strict = 1;
      br_check_proof((br_word_t)(uintptr_t)&st);
    }
  }
  double elapsed = now_ms() - t0;

  uint64_t hash = st.stat_trimmed_cnf ^ (st.stat_trimmed_prf << 16) ^
                  (st.stat_chk_total << 24) ^ (st.stat_resolved << 1) ^
                  st.stat_lit_assigned;
  printf("ms=%.2f hash=0x%016" PRIx64 " resolved=%" PRIu64 " assigned=%" PRIu64
         "\n",
         elapsed, hash, st.stat_resolved, st.stat_lit_assigned);

  free(used);
  free(ants);
  free(lits);
  free(values_buf);
  free(marks_buf);
  free(trail);
  free(work);
  free(pool);
  return 0;
}
