#include <stdint.h>
#include <stdio.h>
extern uint64_t nested(uint64_t n, uint64_t m, uint64_t k);
static uint64_t ref(uint64_t n, uint64_t m, uint64_t k) {
  uint64_t t = 0;
  for (uint64_t i = n; i; i--)
    for (uint64_t j = m; j; j--) t += k + i;
  return t;
}
int main(void) {
  static const uint64_t v[][3] = {{0, 3, 1}, {3, 0, 1}, {1, 1, 5}, {4, 5, 6}, {30, 20, 1000}};
  int bad = 0;
  for (unsigned i = 0; i < sizeof v / sizeof v[0]; i++) {
    uint64_t r = nested(v[i][0], v[i][1], v[i][2]), e = ref(v[i][0], v[i][1], v[i][2]);
    printf("nested(%llu, %llu, %llu) = %llu %s\n", (unsigned long long)v[i][0], (unsigned long long)v[i][1],
           (unsigned long long)v[i][2], (unsigned long long)r, r == e ? "ok" : "BAD");
    bad |= r != e;
  }
  return bad;
}
