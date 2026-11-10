#include <setjmp.h>
#include <stdint.h>
#include <stdio.h>
extern uint64_t twice(uint64_t a, uint64_t b);
static jmp_buf jb;
static uint64_t fail_arg;
void fail(uint64_t a) {
  fail_arg = a;
  longjmp(jb, 1);
}
int main(void) {
  static const struct { uint64_t a, b; int should_fail; uint64_t exp; } tc[] = {
    {20, 22, 0, 42},
    {1, 2, 0, 3},
    {0, 22, 1, 0},
    {20, 0, 1, 0},
    {0x100000000ULL, 5, 1, 0x100000000ULL},
  };
  int bad = 0;
  for (unsigned i = 0; i < sizeof tc / sizeof tc[0]; i++) {
    fail_arg = 0xdeadbeefULL;
    if (setjmp(jb) == 0) {
      uint64_t r = twice(tc[i].a, tc[i].b);
      int ok = !tc[i].should_fail && r == tc[i].exp;
      printf("twice(%llu, %llu) = %llu %s\n",
             (unsigned long long)tc[i].a, (unsigned long long)tc[i].b,
             (unsigned long long)r, ok ? "ok" : "BAD");
      bad |= !ok;
    } else {
      int ok = tc[i].should_fail && fail_arg == tc[i].exp;
      printf("twice(%llu, %llu) -> fail(%llu) %s\n",
             (unsigned long long)tc[i].a, (unsigned long long)tc[i].b,
             (unsigned long long)fail_arg, ok ? "ok" : "BAD");
      bad |= !ok;
    }
  }
  return bad;
}
