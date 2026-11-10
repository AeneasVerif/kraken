#include <stdint.h>
#include <stdio.h>
extern uint64_t callinc(uint64_t a, uint64_t b);
int main(void) {
  static const uint64_t a[] = {0, 40, 100, 0xffffffffULL};
  static const uint64_t b[] = {0, 1, 200, 5};
  int bad = 0;
  for (unsigned i = 0; i < sizeof a / sizeof a[0]; i++) {
    uint64_t r = callinc(a[i], b[i]), e = a[i] + 1 + b[i];
    printf("callinc(%llu, %llu) = %llu %s\n",
           (unsigned long long)a[i], (unsigned long long)b[i],
           (unsigned long long)r, r == e ? "ok" : "BAD");
    bad |= r != e;
  }
  return bad;
}
