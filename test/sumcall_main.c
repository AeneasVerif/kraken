#include <stdint.h>
#include <stdio.h>
extern uint64_t sumcall(uint64_t n, uint64_t b);
int main(void) {
  static const uint64_t n[] = {0, 1, 4, 10, 100};
  static const uint64_t b[] = {5, 10, 2, 100, 7};
  int bad = 0;
  for (unsigned i = 0; i < sizeof n / sizeof n[0]; i++) {
    uint64_t r = sumcall(n[i], b[i]);
    uint64_t e = n[i] * (n[i] + 1) / 2 + n[i] + b[i];
    printf("sumcall(%llu, %llu) = %llu %s\n",
           (unsigned long long)n[i], (unsigned long long)b[i],
           (unsigned long long)r, r == e ? "ok" : "BAD");
    bad |= r != e;
  }
  return bad;
}
