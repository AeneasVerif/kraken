/* kissat-leanqbe: command-line front end for the verified LeanQbe Kissat solver.
 *
 * Links against the machine code that LeanQbe.T emits for `kissat_solve_bytes` (see
 * bench/kissat/build_solver.sh). The input is mapped read-only and the workspace read-write,
 * each between PROT_NONE guard pages. Exit codes follow the SAT competition convention:
 * 20 = UNSATISFIABLE, 0 = UNKNOWN (malformed input, out of fuel or memory, or uncertified SAT
 * under -DKISSAT_UNSAT_ONLY=1), 10 = SATISFIABLE (certified SAT+UNSAT builds; prints DIMACS
 * `v ... 0` model unless `-n`/`--no-model` is passed), 1 = usage, RLIMIT_STACK, or I/O error. */
#define _POSIX_C_SOURCE 200809L
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <unistd.h>

extern uint64_t kissat_solve_bytes(const uint8_t *cnf_ptr, uint64_t cnf_len,
                                   uint8_t *work_ptr, uint64_t work_len, uint64_t fuel);

static int usage(const char *msg) {
  if (msg) fprintf(stderr, "kissat-leanqbe: %s\n", msg);
  fprintf(stderr,
          "usage: kissat-leanqbe [--work-mb <MB>] [--fuel <N>] [-n|--no-model] <input.cnf | ->\n");
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
 * at the upper guard page (or at `base + pg` when `len == 0` so no PROT_NONE pointer is formed).
 * Returns NULL on failure. */
static uint8_t *map_guarded(const uint8_t *init, size_t len, int writable) {
  size_t pg = (size_t)sysconf(_SC_PAGESIZE);
  size_t data = ((len ? len : 1) + pg - 1) / pg * pg;
  uint8_t *base = mmap(NULL, data + 2 * pg, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (base == MAP_FAILED) return NULL;
  if (mprotect(base + pg, data, PROT_READ | PROT_WRITE) != 0) {
    munmap(base, data + 2 * pg);
    return NULL;
  }
  uint8_t *ptr = len ? (base + pg + data - len) : (base + pg);
  if (init && len) memcpy(ptr, init, len);
  if (!writable && mprotect(base + pg, data, PROT_READ) != 0) {
    munmap(base, data + 2 * pg);
    return NULL;
  }
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

#if !defined(KISSAT_UNSAT_ONLY) || !KISSAT_UNSAT_ONLY
static void print_dimacs_model(const int8_t *vals, uint64_t mv) {
  size_t col = 0;
  for (uint64_t v = 1ULL; v <= mv; v++) {
    int8_t b = vals[2ULL * (v - 1ULL)];
    char buf[32];
    int n = snprintf(buf, sizeof(buf), "%s%llu", (b > 0) ? "" : "-", (unsigned long long)v);
    if (n <= 0) continue;
    if (col == 0) {
      fputs("v ", stdout);
      col = 2;
    } else if (col + 1 + (size_t)n > 78) {
      fputs("\nv ", stdout);
      col = 2;
    } else {
      putchar(' ');
      col++;
    }
    fputs(buf, stdout);
    col += (size_t)n;
  }
  if (col == 0) {
    puts("v 0");
  } else if (col + 2 > 78) {
    puts("\nv 0");
  } else {
    puts(" 0");
  }
}
#endif

int main(int argc, char **argv) {
  uint64_t work_mb = 64, fuel = 10000000;
  int no_model = 0;
  const char *path = NULL;
  for (int i = 1; i < argc; i++) {
    if (!strcmp(argv[i], "-h") || !strcmp(argv[i], "--help")) { usage(NULL); return 0; }
    if (!strcmp(argv[i], "-n") || !strcmp(argv[i], "--no-model")) {
      no_model = 1;
    } else if (!strcmp(argv[i], "--work-mb")) {
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
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) != 0 ||
      (rl.rlim_cur != RLIM_INFINITY && rl.rlim_cur < 65536)) {
    fprintf(stderr, "kissat-leanqbe: insufficient RLIMIT_STACK (< 65536 B)\n");
    return 1;
  }
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
#if defined(KISSAT_UNSAT_ONLY) && KISSAT_UNSAT_ONLY
  /* SAT (r == 10) is intentionally uncertified for UNSAT-only inprocessing solvers. */
  (void)no_model;
  if (r == 10) { puts("s UNKNOWN"); return 0; }
#else
  if (r == 10) {
    if (no_model) {
      puts("s SATISFIABLE");
      return 10;
    }
    uintptr_t wp = (uintptr_t)work;
    uintptr_t pad = (wp & 7u) ? (8u - (wp & 7u)) : 0u;
    if (work_len < pad) {
      fprintf(stderr, "kissat-leanqbe: invalid workspace alignment\n");
      return 1;
    }
    const uint64_t *hdr = (const uint64_t *)(work + pad);
#if !defined(KISSAT_CLI_PLAIN_LAYOUT) || !KISSAT_CLI_PLAIN_LAYOUT
    if (work_len - pad >= 8ULL && hdr[0] == 0x4D36484452455831ULL) {
      /* FullM6Hdr ("M6HDREX1"): FullHdr starts at word 288 (2304 bytes). */
      if (work_len - pad < 288ULL * 8ULL) {
        fprintf(stderr, "kissat-leanqbe: truncated M6 header\n");
        return 1;
      }
      pad += 288ULL * 8ULL;
      hdr += 288;
    }
#endif
    if (work_len - pad < 72ULL) {
      fprintf(stderr, "kissat-leanqbe: truncated SAT header\n");
      return 1;
    }
    uint64_t mv = hdr[0];
    uintptr_t vals_ptr = (uintptr_t)hdr[8];
    uintptr_t ws_lo = (uintptr_t)hdr + 72ULL;
    uintptr_t ws_hi = (uintptr_t)work + work_len;
    if (vals_ptr < ws_lo || vals_ptr > ws_hi || mv > (uint64_t)(ws_hi - vals_ptr) / 2ULL) {
      fprintf(stderr, "kissat-leanqbe: invalid SAT model pointer\n");
      return 1;
    }
    puts("s SATISFIABLE");
    print_dimacs_model((const int8_t *)vals_ptr, mv);
    return 10;
  }
#endif
  puts("s UNKNOWN");
  return 0;
}
