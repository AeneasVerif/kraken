/* kissat-leanqbe: command-line front end for the verified LeanQbe Kissat solver.
 *
 * Links against the machine code that LeanQbe.T emits for `kissat_solve_bytes` (see
 * bench/kissat/build_solver.sh). The input is mapped read-only and the workspace read-write,
 * each between PROT_NONE guard pages. Exit codes follow the SAT competition convention:
 * 10 = SATISFIABLE, 20 = UNSATISFIABLE, 0 = UNKNOWN (malformed input, out of fuel or memory),
 * 1 = usage or I/O error. */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

extern uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                                   uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);

static int usage(const char *msg) {
  if (msg) fprintf(stderr, "kissat-leanqbe: %s\n", msg);
  fprintf(stderr, "usage: kissat-leanqbe [--work-mb <MB>] [--fuel <N>] <input.cnf | ->\n");
  return 1;
}

static int parse_u64(const char *s, uint64_t *out) {
  char *end = NULL;
  if (!s || !*s || *s == '-') return 0;
  errno = 0;
  unsigned long long v = strtoull(s, &end, 10);
  if (errno || *end) return 0;
  *out = (uint64_t)v;
  return 1;
}

/* Maps `len` bytes (copied from `init` if non-NULL) between two PROT_NONE guard pages, ending
 * exactly at the upper guard page so any overrun faults. Returns NULL on failure. */
static uint8_t *map_guarded(const uint8_t *init, size_t len, int writable) {
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);
  size_t data = ((len ? len : 1) + pg - 1) / pg * pg;
  uint8_t *base = mmap(NULL, data + 2 * pg, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (base == MAP_FAILED) return NULL;
  if (mprotect(base + pg, data, PROT_READ | PROT_WRITE) != 0) return NULL;
  uint8_t *ptr = base + pg + data - len;
  if (init && len) memcpy(ptr, init, len);
  if (!writable && mprotect(base + pg, data, PROT_READ) != 0) return NULL;
  return ptr;
}

static uint8_t *read_all(FILE *f, size_t *len) {
  size_t cap = 1 << 16, n = 0, got;
  uint8_t *buf = malloc(cap);
  while (buf && (got = fread(buf + n, 1, cap - n, f)) > 0) {
    n += got;
    if (n == cap) {
      uint8_t *nb = realloc(buf, cap *= 2);
      if (!nb) free(buf);
      buf = nb;
    }
  }
  if (!buf || ferror(f)) { free(buf); return NULL; }
  *len = n;
  return buf;
}

int main(int argc, char **argv) {
  uint64_t work_mb = 64, fuel = 10000000;
  const char *path = NULL;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) { usage(NULL); return 0; }
    if (!strcmp(argv[i], "--work-mb")) {
      if (++i >= argc || !parse_u64(argv[i], &work_mb) || !work_mb || work_mb > (1u << 20))
        return usage("--work-mb expects an integer in [1, 1048576]");
    } else if (!strcmp(argv[i], "--fuel")) {
      if (++i >= argc || !parse_u64(argv[i], &fuel)) return usage("--fuel expects an integer");
    } else if (argv[i][0] == '-' && argv[i][1] != '\0') {
      return usage("unknown option");
    } else if (path) {
      return usage("exactly one input file expected");
    } else {
      path = argv[i];
    }
  }
  if (!path) return usage("missing input file");
  FILE *f = strcmp(path, "-") ? fopen(path, "rb") : stdin;
  if (!f) { fprintf(stderr, "kissat-leanqbe: cannot open %s\n", path); return 1; }
  size_t cnf_len = 0;
  uint8_t *raw = read_all(f, &cnf_len);
  if (f != stdin) fclose(f);
  if (!raw) { fprintf(stderr, "kissat-leanqbe: cannot read %s\n", path); return 1; }
  size_t work_len = (size_t)work_mb << 20;
  uint8_t *cnf = map_guarded(raw, cnf_len, 0);
  uint8_t *work = map_guarded(NULL, work_len, 1);
  free(raw);
  if (!cnf || !work) { fprintf(stderr, "kissat-leanqbe: out of memory\n"); return 1; }
  uint64_t r = kissat_solve_bytes(cnf, cnf_len, work, work_len, fuel);
  if (r == 20) { puts("s UNSATISFIABLE"); return 20; }
  if (r == 10) { puts("s SATISFIABLE"); return 10; }
  puts("s UNKNOWN");
  return 0;
}
