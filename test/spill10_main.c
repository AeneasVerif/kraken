#include <stdint.h>
#include <stdio.h>
extern uint64_t spill10(uint64_t a, uint64_t b);
static uint64_t ref_spill10(uint64_t a, uint64_t b) {
  uint64_t r = 0;
  for (uint64_t i = 1; i <= 10; i++) r ^= (a + i);
  return r ^ b;
}
int main(void) {
  static const uint64_t a[] = {0, 10, 42, 1234567};
  static const uint64_t b[] = {0, 7, 99, 0xfeedfacecafebeefULL};
  int bad = 0;
  for (unsigned i = 0; i < sizeof a / sizeof a[0]; i++) {
    uint64_t r = spill10(a[i], b[i]), e = ref_spill10(a[i], b[i]);
    printf("spill10(%llu, %llu) = %llu %s\n",
           (unsigned long long)a[i], (unsigned long long)b[i],
           (unsigned long long)r, r == e ? "ok" : "BAD");
    bad |= r != e;
  }
  return bad;
}
