#define _POSIX_C_SOURCE 200809L
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
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

/* FullHdr layout (144 u64 words = 1152 bytes, LeanQbe/T/Examples/Kissat/Full1.lean:35-69).
 * Note: M2 (FullFastSched / FullFast) aliases hdr[140] (fwd_sub_cnt) -> last_probe_ticks
 * and hdr[141] (fwd_str_cnt) -> last_elim_ticks. */
#define FULL_HDR_BYTES 1152ULL
#define KT_EXT_MAGIC   0x4B54454C4D303031ULL
#define KT_EXT_WORDS   32ULL

typedef struct {
  int ok;
  int status;
  double ms;
  uint64_t conflicts;
  uint64_t decisions;
  uint64_t propagations;
  uint64_t reductions;
  uint64_t restarts;
  uint64_t vivified;
  uint64_t substituted;
  uint64_t congruent;
  uint64_t swept;
  uint64_t eliminated;
  uint64_t factored;
  uint64_t transitive_reduced;
} kissat_ref_stats_t;

static int parse_kissat_stat(const char *line, const char *key, uint64_t *out) {
  if (line[0] != 'c' || line[1] != ' ') return 0;
  const char *p = line + 2;
  while (*p == ' ') p++;
  size_t klen = strlen(key);
  if (strncmp(p, key, klen) != 0 || p[klen] != ':') return 0;
  p += klen + 1;
  while (*p == ' ') p++;
  if (*p < '0' || *p > '9') return 0;
  *out = (uint64_t)strtoull(p, NULL, 10);
  return 1;
}

static kissat_ref_stats_t run_kissat_ref(const char *kbin, const char *cnf_path) {
  kissat_ref_stats_t st;
  memset(&st, 0, sizeof(st));
  if (!kbin || access(kbin, X_OK) != 0) return st;

  int pfd[2];
  if (pipe(pfd) != 0) return st;

  struct timespec t0, t1;
  clock_gettime(CLOCK_MONOTONIC, &t0);
  pid_t pid = fork();
  if (pid < 0) {
    close(pfd[0]);
    close(pfd[1]);
    return st;
  }
  if (pid == 0) {
    close(pfd[0]);
    dup2(pfd[1], STDOUT_FILENO);
    close(pfd[1]);
    char *argv_k[5];
    argv_k[0] = (char *)kbin;
    argv_k[1] = (char *)"-n";
    argv_k[2] = (char *)"-v";
    argv_k[3] = (char *)cnf_path;
    argv_k[4] = NULL;
    execv(kbin, argv_k);
    _exit(127);
  }
  close(pfd[1]);
  FILE *fp = fdopen(pfd[0], "r");
  if (fp) {
    char buf[512];
    while (fgets(buf, sizeof(buf), fp)) {
      if (parse_kissat_stat(buf, "conflicts", &st.conflicts)) continue;
      if (parse_kissat_stat(buf, "decisions", &st.decisions)) continue;
      if (parse_kissat_stat(buf, "propagations", &st.propagations)) continue;
      if (parse_kissat_stat(buf, "reductions", &st.reductions)) continue;
      if (parse_kissat_stat(buf, "restarts", &st.restarts)) continue;
      if (parse_kissat_stat(buf, "vivified", &st.vivified)) continue;
      if (parse_kissat_stat(buf, "substituted", &st.substituted)) continue;
      if (parse_kissat_stat(buf, "congruent", &st.congruent)) continue;
      if (parse_kissat_stat(buf, "swept", &st.swept)) continue;
      if (parse_kissat_stat(buf, "eliminated", &st.eliminated)) continue;
      if (parse_kissat_stat(buf, "factored", &st.factored)) continue;
      if (parse_kissat_stat(buf, "transitive_reduced", &st.transitive_reduced)) continue;
    }
    fclose(fp);
  } else {
    close(pfd[0]);
  }
  int wstatus = 0;
  if (waitpid(pid, &wstatus, 0) > 0 && WIFEXITED(wstatus)) {
    int code = WEXITSTATUS(wstatus);
    if (code == 10 || code == 20 || code == 0) {
      st.ok = 1;
      st.status = code;
    }
  }
  clock_gettime(CLOCK_MONOTONIC, &t1);
  st.ms = (double)(t1.tv_sec - t0.tv_sec) * 1000.0 +
          (double)(t1.tv_nsec - t0.tv_nsec) / 1e6;
  return st;
}

static void print_extended_telemetry(const uint64_t *hdr, size_t work_len, uintptr_t pad) {
  if (work_len < pad + FULL_HDR_BYTES) return;
  uintptr_t del_addr = (uintptr_t)hdr[16];
  uint64_t del_cap = hdr[56];
  uintptr_t ws_lo = (uintptr_t)hdr;
  uintptr_t ws_hi = ws_lo + (work_len - pad);
  uint64_t ext[KT_EXT_WORDS];
  if (!del_addr || del_cap < 22ULL ||
      del_addr < ws_lo || del_addr > ws_hi || (ws_hi - del_addr) < sizeof(ext)) {
    printf("\text_telem=0");
    return;
  }
  memcpy(ext, (const void *)del_addr, sizeof(ext));
  if (ext[0] != KT_EXT_MAGIC) {
    printf("\text_telem=0");
    return;
  }
  printf(
      "\text_telem=1"
      "\tdecisions=%llu\tpropagations=%llu\tchrono_bt_cnt=%llu"
      "\tkitten_calls=%llu\tkitten_ticks=%llu\tbackbone_units=%llu"
      "\treduced_clauses=%llu\tprobe_ticks=%llu\tprobe_wall_ns=%llu"
      "\telim_ticks=%llu\telim_wall_ns=%llu\tvivify_ticks=%llu"
      "\tvivify_wall_ns=%llu\tsweep_ticks=%llu\tsweep_wall_ns=%llu"
      "\tcong_ticks=%llu\tcong_wall_ns=%llu\tfactor_ticks=%llu"
      "\tfactor_wall_ns=%llu\tsubst_wall_ns=%llu\ttrans_wall_ns=%llu"
      "\tbackbone_wall_ns=%llu\tfwd_sub_wall_ns=%llu\tcompact_cnt=%llu"
      "\tcompact_wall_ns=%llu\totfs_subsume=%llu\trestarts_reused_levels=%llu"
      "\tstable_decisions=%llu\tfocused_decisions=%llu\tprobe_calls=%llu"
      "\tvivify_calls=%llu",
      (unsigned long long)ext[1], (unsigned long long)ext[2],
      (unsigned long long)ext[3], (unsigned long long)ext[4],
      (unsigned long long)ext[5], (unsigned long long)ext[6],
      (unsigned long long)ext[7], (unsigned long long)ext[8],
      (unsigned long long)ext[9], (unsigned long long)ext[10],
      (unsigned long long)ext[11], (unsigned long long)ext[12],
      (unsigned long long)ext[13], (unsigned long long)ext[14],
      (unsigned long long)ext[15], (unsigned long long)ext[16],
      (unsigned long long)ext[17], (unsigned long long)ext[18],
      (unsigned long long)ext[19], (unsigned long long)ext[20],
      (unsigned long long)ext[21], (unsigned long long)ext[22],
      (unsigned long long)ext[23], (unsigned long long)ext[24],
      (unsigned long long)ext[25], (unsigned long long)ext[26],
      (unsigned long long)ext[27], (unsigned long long)ext[28],
      (unsigned long long)ext[29], (unsigned long long)ext[30],
      (unsigned long long)ext[31]);
}

static void print_full_telemetry(
    const char *path, uint64_t got, double ms,
    const uint64_t *hdr, size_t work_len, uintptr_t pad,
    int m2_alias, int ext_tel, const kissat_ref_stats_t *kref) {
  uint64_t z[144];
  const uint64_t *h = z;
  memset(z, 0, sizeof(z));
  if (work_len >= pad + FULL_HDR_BYTES) {
    h = hdr;
  }
  const char *slot140 = m2_alias ? "last_probe_ticks" : "fwd_sub";
  const char *slot141 = m2_alias ? "last_elim_ticks" : "fwd_str";
  printf(
      "%s\t%llu\t%.3f"
      "\tconflicts=%llu\tlearned_lits=%llu\tmin_removed=%llu"
      "\tnum_irred=%llu\tnum_redundant=%llu\tnum_binary=%llu"
      "\tswitched=%llu\tsearch_ticks=%llu\trephased=%llu"
      "\treductions=%llu\ttier1=%llu\ttier2=%llu\trestarts=%llu"
      "\toom=%llu\tmax_vars=%llu\tcur_vars=%llu\tunassigned=%llu"
      "\totfs=%llu\teager_sub=%llu\tprobings=%llu\teliminations=%llu\telim_bound=%llu"
      "\thbr=%llu\ttrans=%llu\tviv=%llu\tsubst=%llu"
      "\tcong=%llu\tsweep=%llu\tbve=%llu\tbce=%llu"
      "\tbva=%llu\twalks=%llu\t%s=%llu\t%s=%llu",
      path, (unsigned long long)got, ms,
      (unsigned long long)h[42], (unsigned long long)h[43], (unsigned long long)h[44],
      (unsigned long long)h[61], (unsigned long long)h[62], (unsigned long long)h[63],
      (unsigned long long)h[70], (unsigned long long)h[75], (unsigned long long)h[84],
      (unsigned long long)h[86], (unsigned long long)h[87], (unsigned long long)h[88],
      (unsigned long long)h[89],
      (unsigned long long)h[95], (unsigned long long)h[96], (unsigned long long)h[97],
      (unsigned long long)h[99],
      (unsigned long long)h[120], (unsigned long long)h[121], (unsigned long long)h[123],
      (unsigned long long)h[125], (unsigned long long)h[126],
      (unsigned long long)h[130], (unsigned long long)h[131], (unsigned long long)h[132],
      (unsigned long long)h[133],
      (unsigned long long)h[134], (unsigned long long)h[135], (unsigned long long)h[136],
      (unsigned long long)h[137],
      (unsigned long long)h[138], (unsigned long long)h[139],
      slot140, (unsigned long long)h[140],
      slot141, (unsigned long long)h[141]);
  if (ext_tel) {
    print_extended_telemetry(hdr, work_len, pad);
  }
  if (kref && kref->ok) {
    printf(
        "\tk_status=%d\tk_ms=%.3f\tk_conflicts=%llu\tk_decisions=%llu"
        "\tk_propagations=%llu\tk_reductions=%llu\tk_restarts=%llu"
        "\tk_viv=%llu\tk_subst=%llu\tk_cong=%llu\tk_sweep=%llu"
        "\tk_bve=%llu\tk_bva=%llu\tk_trans=%llu",
        kref->status, kref->ms,
        (unsigned long long)kref->conflicts, (unsigned long long)kref->decisions,
        (unsigned long long)kref->propagations, (unsigned long long)kref->reductions,
        (unsigned long long)kref->restarts, (unsigned long long)kref->vivified,
        (unsigned long long)kref->substituted, (unsigned long long)kref->congruent,
        (unsigned long long)kref->swept, (unsigned long long)kref->eliminated,
        (unsigned long long)kref->factored, (unsigned long long)kref->transitive_reduced);
  }
  putchar('\n');
}

int main(int argc, char **argv) {
  int argi = 1;
  int telemetry = 0;
  int plain_tel = 0;
  int full_tel = 0;
  int ext_tel = 0;
  int m2_alias = 0;
  const char *kissat_bin = NULL;
  while (argi < argc && argv[argi][0] == '-') {
    if (strcmp(argv[argi], "--telemetry") == 0) {
      telemetry = 1;
      argi++;
    } else if (strcmp(argv[argi], "--plain-telemetry") == 0) {
      plain_tel = 1;
      argi++;
    } else if (strcmp(argv[argi], "--full-telemetry") == 0) {
      full_tel = 1;
      argi++;
    } else if (strcmp(argv[argi], "--full-telemetry-m2") == 0) {
      full_tel = 1;
      m2_alias = 1;
      argi++;
    } else if (strcmp(argv[argi], "--extended-telemetry") == 0) {
      full_tel = 1;
      ext_tel = 1;
      argi++;
    } else if (strcmp(argv[argi], "--extended-telemetry-m2") == 0) {
      full_tel = 1;
      ext_tel = 1;
      m2_alias = 1;
      argi++;
    } else if (strcmp(argv[argi], "--m2") == 0) {
      m2_alias = 1;
      argi++;
    } else if (strcmp(argv[argi], "--kissat") == 0 && argi + 1 < argc) {
      kissat_bin = argv[argi + 1];
      argi += 2;
    } else {
      break;
    }
  }
  if (argc - argi < 3) {
    fprintf(stderr,
            "usage: %s [--telemetry|--plain-telemetry|--full-telemetry|--full-telemetry-m2|"
            "--extended-telemetry|--extended-telemetry-m2]"
            " [--m2] [--kissat <bin>] <work_bytes> <fuel> <cnf>...\n",
            argv[0]);
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
    if (full_tel) {
      kissat_ref_stats_t kref = run_kissat_ref(kissat_bin, path);
      print_full_telemetry(path, got, ms, hdr, work_len, pad, m2_alias, ext_tel, &kref);
    } else if (plain_tel) {
      uint64_t rst = 0, red = 0, rph = 0, sw = 0;
      if (work_len >= pad + 768ULL) {
        conflicts = hdr[42];
        learned = hdr[43];
        min_rem = hdr[44];
        sw = hdr[70];
        rph = hdr[84];
        red = hdr[86];
        rst = hdr[89];
      }
      printf("%s\t%llu\t%.3f\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\t%llu\n",
             path, (unsigned long long)got, ms,
             (unsigned long long)conflicts, (unsigned long long)learned,
             (unsigned long long)min_rem, (unsigned long long)rst,
             (unsigned long long)red, (unsigned long long)rph,
             (unsigned long long)sw);
    } else {
      if (telemetry && (got == 10ULL || got == 20ULL) && work_len >= pad + 360ULL) {
        conflicts = hdr[42];
        learned = hdr[43];
        min_rem = hdr[44];
      }
      printf("%s\t%llu\t%.3f\t%llu\t%llu\t%llu\n", path, (unsigned long long)got, ms,
             (unsigned long long)conflicts, (unsigned long long)learned,
             (unsigned long long)min_rem);
    }
    free_guarded(gw);
    free_guarded(gc);
    free(raw);
  }
  return 0;
}
