#include <stdint.h>
#include <stdio.h>
extern uint64_t swap(uint64_t n, uint64_t a, uint64_t b);
int main(void) {
  static const uint64_t v[] = {0, 1, 2, 3, 10, 11};
  int bad = 0;
  for (unsigned i = 0; i < sizeof v / sizeof v[0]; i++) {
    uint64_t r = swap(v[i], 111, 222), e = v[i] % 2 ? 222 : 111;
    printf("swap(%llu, 111, 222) = %llu %s\n", (unsigned long long)v[i], (unsigned long long)r, r == e ? "ok" : "BAD");
    bad |= r != e;
  }
  return bad;
}
