#include <stdint.h>
#include <stdio.h>

extern uint64_t find(uint64_t *p, uint64_t x);
extern void uf_union(uint64_t *p, uint64_t x, uint64_t y) __asm__("union");

int main(void) {
  enum { N = 8 };
  uint64_t parent[N];
  for (uint64_t i = 0; i < N; i++) parent[i] = i;

  /* Build chains: {0,1,2,3} and {4,5,6}, singleton {7}. */
  uf_union(parent, 0, 1);
  uf_union(parent, 1, 2);
  uf_union(parent, 2, 3);
  uf_union(parent, 4, 5);
  uf_union(parent, 5, 6);
  /* Repeat union in same set (no-op branch). */
  uf_union(parent, 0, 3);

  uint64_t r0 = find(parent, 0);
  uint64_t r1 = find(parent, 1);
  uint64_t r2 = find(parent, 2);
  uint64_t r3 = find(parent, 3);
  uint64_t r4 = find(parent, 4);
  uint64_t r5 = find(parent, 5);
  uint64_t r6 = find(parent, 6);
  uint64_t r7 = find(parent, 7);

  int ok = (r0 == 3 && r1 == 3 && r2 == 3 && r3 == 3 &&
            r4 == 6 && r5 == 6 && r6 == 6 && r7 == 7 &&
            r0 != r4 && r0 != r7 && r4 != r7);
  printf("uf before merge: r0..3=%llu,%llu,%llu,%llu r4..6=%llu,%llu,%llu r7=%llu %s\n",
         (unsigned long long)r0, (unsigned long long)r1,
         (unsigned long long)r2, (unsigned long long)r3,
         (unsigned long long)r4, (unsigned long long)r5,
         (unsigned long long)r6, (unsigned long long)r7,
         ok ? "ok" : "BAD");

  /* Merge {0,1,2,3} into {4,5,6}. */
  uf_union(parent, 1, 5);
  for (uint64_t i = 0; i <= 6; i++) {
    uint64_t ri = find(parent, i);
    if (ri != 6) ok = 0;
  }
  if (find(parent, 7) != 7) ok = 0;
  printf("uf after merge(1,5): r0=%llu r6=%llu r7=%llu %s\n",
         (unsigned long long)find(parent, 0),
         (unsigned long long)find(parent, 6),
         (unsigned long long)find(parent, 7),
         ok ? "ok" : "BAD");
  return ok ? 0 : 1;
}
