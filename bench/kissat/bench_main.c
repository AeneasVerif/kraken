#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>
#include <unistd.h>
#include "kissat_verify.h"

extern uint64_t kissat_solve_bytes(
    const uint8_t *cnf_ptr, uint64_t cnf_len,
    uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);

typedef struct {
  void *base;
  size_t total;
  uint8_t *ptr;
  size_t len;
} guarded_buf_t;

static guarded_buf_t alloc_guarded(const uint8_t *init, size_t len, int writable) {
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);
  size_t data_pages = ((len == 0 ? 1 : len) + pg - 1) / pg;
  size_t total = (data_pages + 2) * pg;
  uint8_t *base = (uint8_t *)mmap(NULL, total, PROT_NONE,
      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  assert(base != MAP_FAILED);
  uint8_t *mid = base + pg;
  int rc = mprotect(mid, data_pages * pg, PROT_READ | PROT_WRITE);
  assert(rc == 0);
  memset(mid, 0xAA, data_pages * pg);
  uint8_t *ptr = mid + data_pages * pg - len;
  if (init && len > 0) {
    memcpy(ptr, init, len);
  }
  if (!writable) {
    rc = mprotect(mid, data_pages * pg, PROT_READ);
    assert(rc == 0);
  }
  guarded_buf_t g = { base, total, ptr, len };
  return g;
}

static void free_guarded(guarded_buf_t g) {
  int rc = munmap(g.base, g.total);
  assert(rc == 0);
}

static uint8_t *read_file_bytes(const char *path, size_t *out_len) {
  FILE *f = fopen(path, "rb");
  if (!f) {
    fprintf(stderr, "ERROR: cannot open %s\n", path);
    exit(2);
  }
  if (fseek(f, 0, SEEK_END) != 0) exit(2);
  long sz = ftell(f);
  if (sz < 0) exit(2);
  rewind(f);
  size_t n = (size_t)sz;
  uint8_t *buf = (uint8_t *)malloc(n == 0 ? 1 : n);
  assert(buf != NULL);
  if (n > 0 && fread(buf, 1, n, f) != n) exit(2);
  fclose(f);
  *out_len = n;
  return buf;
}

int main(int argc, char **argv) {
  int argi = 1;
  int telemetry = 0;
  if (argi < argc && strcmp(argv[argi], "--telemetry") == 0) {
    telemetry = 1;
    argi++;
  }
  if (argc - argi < 3) {
    fprintf(stderr, "usage: %s [--telemetry] <work_bytes> <fuel> <cnf>...\n", argv[0]);
    return 2;
  }
  size_t work_len = (size_t)strtoull(argv[argi++], NULL, 10);
  uint64_t fuel = (uint64_t)strtoull(argv[argi++], NULL, 10);
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);

  for (int i = argi; i < argc; i++) {
    const char *path = argv[i];
    size_t cnf_len = 0;
    uint8_t *raw = read_file_bytes(path, &cnf_len);
    guarded_buf_t gc = alloc_guarded(raw, cnf_len, 0);
    guarded_buf_t gw = alloc_guarded(NULL, work_len, 1);
    uint8_t *w_mid = (uint8_t *)gw.base + pg;
    if (work_len > 0) memset(gw.ptr, 0xA5, work_len);

    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    uint64_t got = kissat_solve_bytes(gc.ptr, cnf_len, gw.ptr, work_len, fuel);
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double ms = (double)(t1.tv_sec - t0.tv_sec) * 1000.0 +
                (double)(t1.tv_nsec - t0.tv_nsec) / 1e6;

    if (got != 0ULL && got != 10ULL && got != 20ULL) {
      fprintf(stderr, "FAIL %s: invalid status=%llu\n", path, (unsigned long long)got);
      return 1;
    }
    for (uint8_t *p = w_mid; p < gw.ptr; p++) {
      if (*p != 0xAA) {
        fprintf(stderr, "FAIL %s: wrote before work_ptr\n", path);
        return 1;
      }
    }
    uintptr_t wp = (uintptr_t)gw.ptr;
    uintptr_t pad = (wp & 7u) ? (8u - (wp & 7u)) : 0u;
    const uint64_t *hdr = (const uint64_t *)(gw.ptr + pad);
    if (got == 10ULL) {
      uint64_t mv = hdr[0];
      const int8_t *vals = (const int8_t *)(uintptr_t)hdr[8];
      if (!kissat_verify_dimacs_model((const char *)raw, cnf_len, vals, mv)) {
        fprintf(stderr, "FAIL %s: invalid SAT model\n", path);
        return 1;
      }
    }
    uint64_t conflicts = 0, learned = 0, min_rem = 0;
    if (telemetry && (got == 10ULL || got == 20ULL) && work_len >= pad + 360ULL) {
      conflicts = hdr[42];
      learned = hdr[43];
      min_rem = hdr[44];
    }
    printf("%s\t%llu\t%.3f\t%llu\t%llu\t%llu\n", path, (unsigned long long)got, ms,
           (unsigned long long)conflicts, (unsigned long long)learned,
           (unsigned long long)min_rem);
    free_guarded(gw);
    free_guarded(gc);
    free(raw);
  }
  return 0;
}
