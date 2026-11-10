#include <stdint.h>
#include <stdio.h>
extern uint64_t evenodd(uint64_t n);
int main(void) {
  static const uint64_t v[] = {0, 1, 2, 7, 100, 12345};
  int bad = 0;
  for (unsigned i = 0; i < sizeof v / sizeof v[0]; i++) {
    uint64_t r = evenodd(v[i]), e = v[i] % 2 == 0;
    printf("evenodd(%llu) = %llu %s\n", (unsigned long long)v[i], (unsigned long long)r, r == e ? "ok" : "BAD");
    bad |= r != e;
  }
  return bad;
}
