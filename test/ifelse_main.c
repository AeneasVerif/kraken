#include <stdint.h>
#include <stdio.h>
extern uint64_t ifelse(uint64_t a, uint64_t b);
static uint64_t ref(uint64_t a, uint64_t b) { return (uint32_t)a ? a + b : b - a; }
int main(void) {
  static const uint64_t v[][2] = {{0, 5}, {3, 4}, {0x100000000ull, 7}, {0x100000001ull, 7}, {~0ull, 1}};
  int bad = 0;
  for (unsigned i = 0; i < sizeof v / sizeof v[0]; i++) {
    uint64_t r = ifelse(v[i][0], v[i][1]), e = ref(v[i][0], v[i][1]);
    printf("ifelse(%#llx, %#llx) = %#llx %s\n", (unsigned long long)v[i][0], (unsigned long long)v[i][1],
           (unsigned long long)r, r == e ? "ok" : "BAD");
    bad |= r != e;
  }
  return bad;
}
