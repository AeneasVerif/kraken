#include <stdint.h>

uint64_t sum_to_n(uint64_t n) {
  uint64_t sum = 0;
  if (n == 0) {
    return sum;
  }
  do {
    sum += n;
    // Emit no code, but keep this loop visible for the verification examples.
    __asm__ volatile("" : : "r"(n));
    --n;
  } while (n != 0);
  return sum;
}
