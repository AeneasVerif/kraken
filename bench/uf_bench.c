#define _POSIX_C_SOURCE 200809L
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifdef UF_IN_C
__attribute__((noinline)) uint64_t find(uint64_t *p, uint64_t x) {
  for (;;) {
    uint64_t px = p[x];
    if (px == x)
      return x;
    uint64_t gp = p[px];
    p[x] = gp;
    x = gp;
  }
}

#ifndef UF_NO_CALL
__attribute__((noinline)) void uf_union(uint64_t *p, uint64_t x, uint64_t y) {
  uint64_t rx = find(p, x);
  uint64_t ry = find(p, y);
  if (rx != ry)
    p[rx] = ry;
}
#endif

__attribute__((noinline)) void unionInline(uint64_t *p, uint64_t x, uint64_t y) {
  for (;;) {
    uint64_t px = p[x];
    if (px == x)
      break;
    uint64_t gp = p[px];
    p[x] = gp;
    x = gp;
  }
  for (;;) {
    uint64_t py = p[y];
    if (py == y)
      break;
    uint64_t gp = p[py];
    p[y] = gp;
    y = gp;
  }
  if (x != y)
    p[x] = y;
}
#else
extern uint64_t find(uint64_t *p, uint64_t x);
extern void unionInline(uint64_t *p, uint64_t x, uint64_t y);
#ifndef UF_NO_CALL
extern void uf_union(uint64_t *p, uint64_t x, uint64_t y) __asm__("union");
#endif
#endif

static inline uint64_t splitmix64(uint64_t *state) {
  uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
  z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
  z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
  return z ^ (z >> 31);
}

static double now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (double)ts.tv_sec * 1000.0 + (double)ts.tv_nsec / 1e6;
}

int main(int argc, char **argv) {
  int use_inline = (argc > 1 && strcmp(argv[1], "inline") == 0);
#ifdef UF_NO_CALL
  use_inline = 1;
#endif
  const uint64_t N = 65536;
  const int ROUNDS = 40;
  uint64_t *p = (uint64_t *)malloc(N * sizeof(uint64_t));
  if (!p)
    return 2;

  uint64_t seed = 0x123456789abcdef0ULL;
  uint64_t checksum = 0;
  double t0 = now_ms();

  for (int r = 0; r < ROUNDS; r++) {
    for (uint64_t i = 0; i < N; i++)
      p[i] = i;
    /* Build long chains first so path halving does non-trivial work, then random unions/finds. */
    for (uint64_t i = 0; i + 1 < N; i += 2) {
      uint64_t a = splitmix64(&seed) & (N - 1);
      uint64_t b = splitmix64(&seed) & (N - 1);
      if (use_inline) {
        unionInline(p, a, b);
      } else {
#ifndef UF_NO_CALL
        uf_union(p, a, b);
#endif
      }
    }
    for (uint64_t i = 0; i < 2 * N; i++) {
      uint64_t x = splitmix64(&seed) & (N - 1);
      checksum = (checksum * 1315423911ULL) ^ find(p, x);
    }
  }

  double elapsed = now_ms() - t0;
  free(p);

  const uint64_t expected = 0x77b41e65c29d6ec9ULL;
  if (checksum != expected && getenv("UF_PRINT_HASH")) {
    printf("hash=0x%016" PRIx64 " ms=%.2f\n", checksum, elapsed);
    return 0;
  }
  printf("ms=%.2f hash=0x%016" PRIx64 "\n", elapsed, checksum);
  return 0;
}
