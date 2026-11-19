#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
  uint64_t base;
  uint64_t cur;
  uint64_t end;
  uint64_t fuel;
  uint64_t depth;
  uint64_t env;
} LeanRt;

extern uint64_t lrc_sumTo(uint64_t rt, uint64_t n);
extern uint64_t lrc_mapAdd(uint64_t rt, uint64_t n, uint64_t k);
extern uint64_t lrc_tree2(uint64_t rt, uint64_t d);
extern uint64_t lrc_foldMap(uint64_t rt, uint64_t n, uint64_t k);

extern uint64_t LeanQbe_T_LeanLRC_leanSumTo(uint64_t rt, uint64_t n);
extern uint64_t LeanQbe_T_LeanLRC_leanMapAddSum(uint64_t rt, uint64_t n, uint64_t k);
extern uint64_t LeanQbe_T_LeanLRC_leanTree2(uint64_t rt, uint64_t d);
extern uint64_t LeanQbe_T_LeanLRC_leanFoldMap(uint64_t rt, uint64_t n, uint64_t k);

static jmp_buf g_trap_jmp;
static volatile int g_trap_code = 0;

void lean_out_of_fuel(uint64_t rt) {
  (void)rt;
  if (g_trap_code == -1) longjmp(g_trap_jmp, 1);
  exit(11);
}
void lean_stack_overflow(uint64_t rt) {
  (void)rt;
  if (g_trap_code == -1) longjmp(g_trap_jmp, 2);
  exit(12);
}
void lean_oom(uint64_t rt) { (void)rt; if (g_trap_code == -1) longjmp(g_trap_jmp, 3); exit(13); }
void lean_panic(uint64_t rt) { (void)rt; if (g_trap_code == -1) longjmp(g_trap_jmp, 4); exit(14); }

static uint64_t bx(uint64_t n) { return (n << 1) | 1ULL; }
static uint64_t ub(uint64_t x) { return x >> 1; }

static void init_rt(LeanRt *rt, uint8_t *heap, size_t cap, uint64_t fuel, uint64_t depth) {
  rt->base = (uint64_t)(uintptr_t)heap;
  rt->cur = (uint64_t)(uintptr_t)heap;
  rt->end = (uint64_t)(uintptr_t)(heap + cap);
  rt->fuel = fuel;
  rt->depth = depth;
  rt->env = 0ULL;
}

static void chk(const char *tag, uint64_t got, uint64_t exp) {
  if (got != exp) {
    fprintf(stderr, "FAIL %s: got=%llu exp=%llu\n", tag, (unsigned long long)got,
            (unsigned long long)exp);
    exit(1);
  }
}

int main(void) {
  const size_t cap = 1ULL << 20;
  uint8_t *heap = (uint8_t *)malloc(cap);
  if (!heap) return 2;
  LeanRt rt;
  const uint64_t ns[5] = {0, 1, 5, 10, 12};
  for (int i = 0; i < 5; ++i) {
    uint64_t n = ns[i];
    init_rt(&rt, heap, cap, 1000000ULL, 1024ULL);
    uint64_t r = (uint64_t)(uintptr_t)&rt;
    uint64_t s1 = ub(lrc_sumTo(r, bx(n)));
    uint64_t s2 = ub(LeanQbe_T_LeanLRC_leanSumTo(r, bx(n)));
    uint64_t m1 = ub(lrc_mapAdd(r, bx(n), bx(3)));
    uint64_t m2 = ub(LeanQbe_T_LeanLRC_leanMapAddSum(r, bx(n), bx(3)));
    uint64_t f1 = ub(lrc_foldMap(r, bx(n), bx(4)));
    uint64_t f2 = ub(LeanQbe_T_LeanLRC_leanFoldMap(r, bx(n), bx(4)));
    chk("sumTo", s1, s2);
    chk("mapAdd", m1, m2);
    chk("foldMap", f1, f2);
    chk("depthBalanced", rt.depth, 1024ULL);
    printf("CASE n=%llu sumTo=%llu mapAdd=%llu foldMap=%llu\n",
           (unsigned long long)n, (unsigned long long)s1,
           (unsigned long long)m1, (unsigned long long)f1);
  }
  for (uint64_t d = 0; d <= 6; ++d) {
    init_rt(&rt, heap, cap, 1000000ULL, 1024ULL);
    uint64_t r = (uint64_t)(uintptr_t)&rt;
    uint64_t t1 = ub(lrc_tree2(r, bx(d)));
    uint64_t t2 = ub(LeanQbe_T_LeanLRC_leanTree2(r, bx(d)));
    chk("tree2", t1, t2);
    chk("depthBalancedTree", rt.depth, 1024ULL);
    printf("TREE d=%llu tree2=%llu\n", (unsigned long long)d, (unsigned long long)t1);
  }
  init_rt(&rt, heap, cap, 100000ULL, 1024ULL);
  chk("tailSum500", ub(lrc_sumTo((uint64_t)(uintptr_t)&rt, bx(500))), 125250ULL);
  chk("tailDepth", rt.depth, 1024ULL);

  g_trap_code = -1;
  init_rt(&rt, heap, cap, 4ULL, 128ULL);
  if (setjmp(g_trap_jmp) == 0) {
    (void)lrc_sumTo((uint64_t)(uintptr_t)&rt, bx(20));
    fprintf(stderr, "FAIL: expected lean_out_of_fuel\n");
    return 1;
  } else {
    init_rt(&rt, heap, cap, 10000ULL, 3ULL);
    if (setjmp(g_trap_jmp) == 0) {
      (void)lrc_tree2((uint64_t)(uintptr_t)&rt, bx(4));
      fprintf(stderr, "FAIL: expected lean_stack_overflow\n");
      return 1;
    } else {
      init_rt(&rt, heap, 16ULL, 10000ULL, 128ULL);
      if (setjmp(g_trap_jmp) == 0) {
        (void)lrc_tree2((uint64_t)(uintptr_t)&rt, bx(3));
        fprintf(stderr, "FAIL: expected lean_oom\n");
        return 1;
      }
    }
  }
  g_trap_code = 0;
  free(heap);
  return 0;
}
