// Harness for the tracer litmus program: x = a + b; *p = x; return x.
#include <stdint.h>
#include <stdio.h>

extern uint64_t tracer(uint64_t a, uint64_t b, uint64_t *p);

int main(void) {
  static const uint64_t v[][2] = {
      {40, 2}, {0, 0}, {UINT64_MAX, 1}, {0x8000000000000000ull, 0x8000000000000000ull},
      {0x123456789abcdef0ull, 0x0fedcba987654321ull}};
  int bad = 0;
  for (unsigned i = 0; i < sizeof v / sizeof v[0]; i++) {
    uint64_t cell = 0xdeadbeef, a = v[i][0], b = v[i][1];
    uint64_t r = tracer(a, b, &cell);
    int ok = r == a + b && cell == a + b;
    printf("tracer(%#llx, %#llx) = %#llx, *p = %#llx %s\n", (unsigned long long)a,
           (unsigned long long)b, (unsigned long long)r, (unsigned long long)cell, ok ? "ok" : "BAD");
    bad |= !ok;
  }
  return bad;
}
