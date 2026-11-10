#include <stdint.h>
#include <stdio.h>
extern uint64_t sumto(uint64_t n);
int main(void) {
  static const uint64_t v[] = {0, 1, 2, 10, 1000, 100000};
  int bad = 0;
  for (unsigned i = 0; i < sizeof v / sizeof v[0]; i++) {
    uint64_t r = sumto(v[i]), e = v[i] * (v[i] + 1) / 2;
    printf("sumto(%llu) = %llu %s\n", (unsigned long long)v[i], (unsigned long long)r, r == e ? "ok" : "BAD");
    bad |= r != e;
  }
  return bad;
}
