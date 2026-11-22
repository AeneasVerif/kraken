#!/usr/bin/env python3
"""Work-cap OOM & SAT witness differential fuzzer for Kissat C3b/C4.

Sweeps ``work_cap`` via binary search and fine offsets (``-64 KiB .. +256 KiB``)
around the saturation boundaries of ``arena``, ``watch_stk``, ``extend_stk``, and
``scratch_buf`` on SAT and UNSAT CNFs. Distinguishes ``WITNESS_CHECK_FAIL``
(``status=3``) from ``fuel_exhausted`` (``status=0``), asserts zero SAT/UNSAT
flips, and optionally checks ``h->oom`` monotonicity across solver stages.
"""

import argparse
import glob
import json
import os
import random
import re
import subprocess
import sys
import tempfile

KiB = 1024
MiB = 1024 * 1024
DEFAULT_FINE_OFFSETS = [
    -64 * KiB, -32 * KiB, -16 * KiB, -8 * KiB, -4 * KiB, -1 * KiB,
    0,
    1 * KiB, 4 * KiB, 8 * KiB, 16 * KiB, 32 * KiB, 64 * KiB,
    128 * KiB, 256 * KiB,
]
FAST_FINE_OFFSETS = [-64 * KiB, -16 * KiB, -4 * KiB, 0, 4 * KiB, 16 * KiB, 64 * KiB, 256 * KiB]

DRIVER_CPP = r"""
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

#include "tqbe_rt.hpp"
#include "kissat_verify.h"
#include "check_c3b_invariants.hpp"

namespace tqbe_gen {
#include "__GEN_HPP__"
}

static bool rd_file(const char *path, std::vector<uint8_t> &out) {
  FILE *f = std::fopen(path, "rb");
  if (!f) return false;
  std::fseek(f, 0, SEEK_END);
  long sz = std::ftell(f);
  if (sz < 0) { std::fclose(f); return false; }
  std::rewind(f);
  out.resize(static_cast<size_t>(sz));
  if (sz > 0 && std::fread(out.data(), 1, static_cast<size_t>(sz), f) != static_cast<size_t>(sz)) {
    std::fclose(f);
    return false;
  }
  std::fclose(f);
  return true;
}

static uint64_t rd_hdr_u64(const void *hdr, size_t w) {
  uint64_t val = 0;
  std::memcpy(&val, static_cast<const uint8_t *>(hdr) + w * 8ULL, 8ULL);
  return val;
}

static void wr_hdr_u64(void *hdr, size_t w, uint64_t val) {
  std::memcpy(static_cast<uint8_t *>(hdr) + w * 8ULL, &val, 8ULL);
}

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  const char *cnf_path = argv[1];
  uint64_t work_bytes = 4ULL * 1024ULL * 1024ULL;
  uint64_t fuel = 50000000ULL;
  bool check_oom_mono = false;
  bool force_oom_sticky = false;
  bool check_inv = false;
  bool check_search_inv = false;
  for (int i = 2; i < argc; ++i) {
    if (std::strncmp(argv[i], "--work-bytes=", 13) == 0) {
      work_bytes = std::strtoull(argv[i] + 13, nullptr, 10);
    } else if (std::strncmp(argv[i], "--fuel=", 7) == 0) {
      fuel = std::strtoull(argv[i] + 7, nullptr, 10);
    } else if (std::strcmp(argv[i], "--check-oom-monotone") == 0) {
      check_oom_mono = true;
    } else if (std::strcmp(argv[i], "--test-oom-sticky") == 0) {
      force_oom_sticky = true;
      check_oom_mono = true;
    } else if (std::strcmp(argv[i], "--check-inv") == 0) {
      check_inv = true;
    } else if (std::strcmp(argv[i], "--check-search-inv") == 0) {
      check_search_inv = true;
    }
  }
  std::vector<uint8_t> cnf;
  if (!rd_file(cnf_path, cnf)) return 2;
  std::vector<uint8_t> work(static_cast<size_t>(work_bytes), 0);
  ::tqbe::Mem mem;
  uint64_t cnf_addr = reinterpret_cast<uint64_t>(cnf.data());
  uint64_t cnf_end = cnf_addr + static_cast<uint64_t>(cnf.size());
  uint64_t raw_ptr = reinterpret_cast<uint64_t>(work.data());
  uint64_t pad = (8ULL - (raw_ptr & 7ULL)) & 7ULL;
  uint64_t hdr_addr = raw_ptr + pad;
  uint64_t avail = work_bytes > pad ? (work_bytes - pad) : 0ULL;
  if (work_bytes < pad + 1152ULL) {
    std::printf(
        "{\"status\":0,\"oom\":1,\"init_ok\":0,\"oom_monotone_ok\":1,\"inv_ok\":1,"
        "\"arena_len\":0,\"arena_cap\":0,\"wlen\":0,\"wcap\":0,"
        "\"extend_len\":0,\"extend_cap\":0,\"scratch_cap\":0,\"conflicts\":0,\"ticks\":0}\n");
    return 0;
  }
  uint8_t *hp = work.data() + pad;

  bool init_ok = tqbe_gen::full_init_state(
      mem, ::tqbe::bits<64>(cnf_addr), ::tqbe::bits<64>(cnf_end),
      ::tqbe::bits<64>(hdr_addr), ::tqbe::bits<64>(avail), ::tqbe::bits<64>(fuel));
  uint64_t oom_init = rd_hdr_u64(hp, 95);
  bool mono_ok = true;
  bool inv_ok = true;
  std::string inv_err;

  uint64_t status = 0;
  uint64_t witness_ok = 1;
  uint64_t oom_parse = oom_init;
  uint64_t oom_pre = oom_init;
  uint64_t oom_search = oom_init;
  uint64_t oom_ext = oom_init;
  if (init_ok) {
    uint64_t orig_mv = rd_hdr_u64(hp, 0);
    uint64_t pb = tqbe_gen::full_parse_body(
        mem, ::tqbe::bits<64>(hdr_addr), ::tqbe::bits<64>(cnf_end)).data;
    oom_parse = rd_hdr_u64(hp, 95);
    if (oom_init == 1ULL && oom_parse == 0ULL) mono_ok = false;
    if (check_inv && pb == 1ULL && oom_parse == 0ULL) {
      inv_ok = inv_ok && kissat_c3b_inv::check_bins(hp, &inv_err)
                      && kissat_c3b_inv::check_2wl(hp, &inv_err);
    }
    if (pb != 1ULL) {
      status = pb;
    } else {
      uint64_t pp = tqbe_gen::full_preprocess(mem, ::tqbe::bits<64>(hdr_addr)).data;
      oom_pre = rd_hdr_u64(hp, 95);
      if ((oom_parse == 1ULL || oom_init == 1ULL) && oom_pre == 0ULL) mono_ok = false;
      if (check_inv && pp == 1ULL && oom_pre == 0ULL) {
        inv_ok = inv_ok && kissat_c3b_inv::check_bins(hp, &inv_err)
                        && kissat_c3b_inv::check_2wl(hp, &inv_err);
      }
      if (force_oom_sticky && oom_pre == 0ULL) wr_hdr_u64(hp, 95, 1ULL);
      uint64_t pre_search_oom = rd_hdr_u64(hp, 95);
      status = (pp == 1ULL) ? tqbe_gen::full_search(mem, ::tqbe::bits<64>(hdr_addr)).data : pp;
      oom_search = rd_hdr_u64(hp, 95);
      if (pre_search_oom == 1ULL && oom_search == 0ULL) mono_ok = false;
    }
    if (status == 10ULL) {
      if (check_search_inv && oom_search == 0ULL) {
        inv_ok = inv_ok && kissat_c3b_inv::check_bins(hp, &inv_err)
                        && kissat_c3b_inv::check_2wl(hp, &inv_err);
      }
      tqbe_gen::full_extend(mem, ::tqbe::bits<64>(hdr_addr));
      oom_ext = rd_hdr_u64(hp, 95);
      if (oom_search == 1ULL && oom_ext == 0ULL) mono_ok = false;
      wr_hdr_u64(hp, 0, orig_mv);
      wr_hdr_u64(hp, 98, rd_hdr_u64(hp, 96) - orig_mv);
      uint64_t vals_ptr = rd_hdr_u64(hp, 8);
      uint64_t chk = tqbe_gen::kissat_check_model(
          mem, ::tqbe::bits<64>(cnf_addr), ::tqbe::bits<64>(cnf_end),
          ::tqbe::bits<64>(hdr_addr), ::tqbe::bits<64>(vals_ptr),
          ::tqbe::bits<64>(orig_mv)).data;
      const int8_t *vals = reinterpret_cast<const int8_t *>(static_cast<uintptr_t>(vals_ptr));
      int dchk = kissat_verify_dimacs_model(
          reinterpret_cast<const char *>(cnf.data()), static_cast<uint64_t>(cnf.size()),
          vals, orig_mv);
      if (chk != 1ULL || dchk != 1) {
        status = 3ULL;
        witness_ok = 0ULL;
      }
    }
  } else {
    oom_search = 1ULL;
  }
  uint64_t final_oom = rd_hdr_u64(hp, 95);
  if (!check_oom_mono) mono_ok = true;
  std::printf(
      "{\"status\":%llu,\"oom\":%llu,\"init_ok\":%d,\"witness_ok\":%llu,"
      "\"oom_monotone_ok\":%d,\"inv_ok\":%d,\"inv_err\":\"%s\","
      "\"arena_len\":%llu,\"arena_cap\":%llu,\"wlen\":%llu,\"wcap\":%llu,"
      "\"extend_len\":%llu,\"extend_cap\":%llu,\"scratch_cap\":%llu,"
      "\"conflicts\":%llu,\"ticks\":%llu}\n",
      (unsigned long long)status,
      (unsigned long long)(init_ok ? final_oom : 1ULL),
      init_ok ? 1 : 0,
      (unsigned long long)witness_ok,
      mono_ok ? 1 : 0,
      inv_ok ? 1 : 0,
      inv_err.c_str(),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 6) : 0ULL),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 4) : 0ULL),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 7) : 0ULL),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 5) : 0ULL),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 114) : 0ULL),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 113) : 0ULL),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 116) : 0ULL),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 42) : 0ULL),
      (unsigned long long)(init_ok ? rd_hdr_u64(hp, 75) : 0ULL));
  return 0;
}
"""


def write_dimacs(path, nvars, clauses):
    """Write clauses in DIMACS CNF format."""
    with open(path, "w", encoding="utf-8") as f:
        f.write(f"p cnf {nvars} {len(clauses)}\n")
        for cl in clauses:
            f.write(" ".join(str(x) for x in cl) + " 0\n")


def gen_fuzz_corpus(out_dir, seed=20261122):
    """Generate deterministic SAT and UNSAT CNFs covering key stress patterns."""
    rng = random.Random(seed)
    cases = []

    # 1. Planted SAT 3-SAT with BVE-friendly chains (exercises arena/watches/extend).
    nv1 = 120
    assign1 = {v: rng.choice([True, False]) for v in range(1, nv1 + 1)}
    cl1 = []
    for _ in range(440):
        vs = rng.sample(range(1, nv1 + 1), 3)
        lits = [v if rng.random() < 0.5 else -v for v in vs]
        if not any((l > 0) == assign1[abs(l)] for l in lits):
            idx = rng.randrange(3)
            lits[idx] = -lits[idx]
        cl1.append(lits)
    for k in range(1, 30):
        a, b = k, k + 30
        if assign1[a] != assign1[b]:
            cl1.extend([[-a, -b], [a, b]])
        else:
            cl1.extend([[-a, b], [a, -b]])
    p1 = os.path.join(out_dir, "fuzz_sat_rand3_bve.cnf")
    write_dimacs(p1, nv1, cl1)
    cases.append({"name": "fuzz_sat_rand3_bve", "path": p1, "expected": "SAT"})

    # 2. Planted SAT with heavy equivalence/subst chains (stresses extend_stk).
    nv2 = 300
    assign2 = {v: (v % 3 != 0) for v in range(1, nv2 + 1)}
    cl2 = []
    for v in range(1, 220):
        nxt = v + 1
        same = assign2[v] == assign2[nxt]
        cl2.extend([[-v, nxt if same else -nxt], [v, -nxt if same else nxt]])
    for _ in range(520):
        vs = rng.sample(range(1, nv2 + 1), 3)
        lits = [v if rng.random() < 0.5 else -v for v in vs]
        if not any((l > 0) == assign2[abs(l)] for l in lits):
            lits[0] = -lits[0]
        cl2.append(lits)
    p2 = os.path.join(out_dir, "fuzz_sat_subst_chain.cnf")
    write_dimacs(p2, nv2, cl2)
    cases.append({"name": "fuzz_sat_subst_chain", "path": p2, "expected": "SAT"})

    # 3. PHP(5, 4) + equivalence extension (UNSAT, compaction + arena/watch churn).
    p_n, h_n = 5, 4
    cl3 = [[i * h_n + j + 1 for j in range(h_n)] for i in range(p_n)]
    for j in range(h_n):
        for i1 in range(p_n):
            for i2 in range(i1 + 1, p_n):
                cl3.append([-(i1 * h_n + j + 1), -(i2 * h_n + j + 1)])
    for v in range(21, 141):
        base = ((v - 21) % 20) + 1
        cl3.extend([[-v, base], [v, -base]])
    p3 = os.path.join(out_dir, "fuzz_unsat_php54_ext.cnf")
    write_dimacs(p3, 140, cl3)
    cases.append({"name": "fuzz_unsat_php54_ext", "path": p3, "expected": "UNSAT"})

    # 4. Odd-charge Tseitin XOR graph (UNSAT, stresses binary/xor/kitten).
    nv4 = 28
    cl4 = []
    deg = [0] * nv4
    edges = []
    for i in range(nv4):
        edges.append((i, (i + 1) % nv4))
        if i % 2 == 0 and i + 2 < nv4:
            edges.append((i, i + 2))
    # Assign 1 var per edge and assert XOR over incident edges.
    e_var = {idx: idx + 1 for idx in range(len(edges))}
    inc = [[] for _ in range(nv4)]
    for idx, (u, v) in enumerate(edges):
        inc[u].append(e_var[idx])
        inc[v].append(e_var[idx])
    for u in range(nv4):
        lits = inc[u]
        parity = 1 if u == 0 else 0
        for mask in range(1 << len(lits)):
            if bin(mask).count("1") % 2 != parity:
                cl4.append([-l if ((mask >> k) & 1) else l for k, l in enumerate(lits)])
    p4 = os.path.join(out_dir, "fuzz_unsat_tseitin.cnf")
    write_dimacs(p4, len(edges), cl4)
    cases.append({"name": "fuzz_unsat_tseitin", "path": p4, "expected": "UNSAT"})

    return cases


def compile_driver(gen_hpp, tmp_dir, runtime_dir, verify_dir, check_inv):
    """Compile standalone C3b fuzzer driver against gen_hpp."""
    hpp_abs = os.path.abspath(gen_hpp)
    cpp_path = os.path.join(tmp_dir, "fuzz_driver.cpp")
    bin_path = os.path.join(tmp_dir, "fuzz_driver")
    with open(cpp_path, "w", encoding="utf-8") as f:
        f.write(DRIVER_CPP.replace("__GEN_HPP__", hpp_abs))
    cmd = [
        "timeout", "180", "clang++", "-std=c++20", "-O3",
        "-Wall", "-Wextra", "-DTQBE_NATIVE_MEM",
        f"-I{runtime_dir}", f"-I{verify_dir}",
        f"-I{os.path.dirname(hpp_abs)}",
    ]
    if check_inv:
        cmd.append("-DKISSAT_C3B_CHECK_INV")
    cmd.extend([cpp_path, "-o", bin_path])
    subprocess.run(cmd, check=True)
    return bin_path


def parse_dimacs_header(cnf_path):
    """Return (mv, nc) from a DIMACS CNF file."""
    with open(cnf_path, "r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            s = line.strip()
            if s.startswith("p cnf "):
                parts = s.split()
                if len(parts) >= 4:
                    return int(parts[2]), int(parts[3])
    return 0, 0


def run_driver(driver_bin, cnf_path, work_bytes, fuel, timeout_s, oom_mono=False,
               check_inv=False, sticky=False, check_search_inv=False):
    """Execute compiled driver once and return parsed status/watermark dict."""
    cmd = [
        "timeout", str(timeout_s), driver_bin, cnf_path,
        f"--work-bytes={work_bytes}", f"--fuel={fuel}",
    ]
    if oom_mono:
        cmd.append("--check-oom-monotone")
    if sticky:
        cmd.append("--test-oom-sticky")
    if check_inv:
        cmd.append("--check-inv")
    if check_search_inv:
        cmd.append("--check-search-inv")
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode == 124:
        return {"status": 0, "timeout": True, "crash": False, "oom": 0}
    if proc.returncode != 0:
        return {"status": -1, "timeout": False, "crash": True,
                "rc": proc.returncode, "stderr": proc.stderr[-200:]}
    for line in proc.stdout.splitlines():
        if line.strip().startswith("{"):
            rec = json.loads(line.strip())
            rec["timeout"] = False
            rec["crash"] = False
            return rec
    return {"status": -1, "timeout": False, "crash": True, "stderr": "no json line"}


def run_bench_cli(c3b_bin, cnf_path, work_bytes, fuel, timeout_s):
    """Fallback runner using bench_main-compatible binary."""
    cmd = [
        "timeout", str(timeout_s), c3b_bin, "--full-telemetry-m2",
        str(work_bytes), str(fuel), cnf_path,
    ]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    rec = {"status": 0, "timeout": proc.returncode == 124, "crash": False,
           "oom": 0, "oom_monotone_ok": 1, "inv_ok": 1,
           "arena_len": 0, "arena_cap": 0, "wlen": 0, "wcap": 0,
           "extend_len": 0, "extend_cap": 0, "scratch_cap": 0}
    if proc.returncode not in (0, 3, 10, 20, 124):
        rec["crash"] = True
        rec["status"] = -1
        return rec
    if proc.returncode == 124:
        return rec
    lines = [l.strip() for l in proc.stdout.splitlines() if l.strip()]
    if lines and "\t" in lines[0]:
        parts = lines[0].split("\t")
        if len(parts) >= 3 and parts[1].isdigit():
            rec["status"] = int(parts[1])
            for tok in parts[3:]:
                if "=" in tok:
                    k, v = tok.split("=", 1)
                    if k in rec and v.isdigit():
                        rec[k] = int(v)
            return rec
    rec["status"] = proc.returncode
    return rec


def oracle_kissat(kissat_bin, cnf_path, timeout_s):
    """Get ground-truth SAT/UNSAT verdict from C1 Kissat."""
    proc = subprocess.run(
        ["timeout", str(timeout_s), kissat_bin, "-q", "-n", cnf_path],
        capture_output=True, text=True,
    )
    if proc.returncode == 10:
        return "SAT"
    if proc.returncode == 20:
        return "UNSAT"
    return "UNKNOWN"


def estimate_boundaries(mv, base_rec, max_bytes):
    """Estimate work_cap saturation boundaries for arena/watch_stk/extend_stk/scratch_buf."""
    fixed = 1536 + mv * 176
    bounds = {}
    alen = max(base_rec.get("arena_len", 0), 64)
    wlen = max(base_rec.get("wlen", 0), 64)
    elen = max(base_rec.get("extend_len", 0), 32)
    # Full1 formulas: scratch >= 40 KiB at rem >= 656 KiB; ext_cap ~ min(rem>>5, ...).
    bounds["scratch_buf"] = fixed + 656 * KiB
    bounds["extend_stk"] = fixed + elen * 4 * 32
    bounds["arena"] = fixed + 64 * KiB + int((alen * 4) / 0.6)
    bounds["watch_stk"] = fixed + 64 * KiB + int((wlen * 4) / 0.3)
    return {k: max(4 * KiB, min(max_bytes, v)) for k, v in bounds.items()}


def binary_search_min_cap(run_fn, cnf_path, lo, hi, fuel, timeout_s, want_solved=True):
    """Binary search lowest work_cap achieving solved (or oom==0)."""
    best = hi
    cur_lo = lo
    cur_hi = hi
    while cur_hi - cur_lo > 4096:
        mid = ((cur_lo + cur_hi) // 2) & ~4095
        if mid <= cur_lo:
            mid = cur_lo + 4096
        rec = run_fn(cnf_path, mid, fuel, timeout_s)
        ok = (rec.get("status") in (10, 20)) if want_solved else (
            rec.get("oom", 1) == 0 and not rec.get("crash"))
        if ok:
            best = mid
            cur_hi = mid
        else:
            cur_lo = mid
    return best


def main():
    ap = argparse.ArgumentParser(description="Work-cap OOM & SAT witness fuzzer for C3b.")
    ap.add_argument("--gen-hpp", default="", help="Path to emitted C3b *_gen.hpp")
    ap.add_argument("--c3b-bin", default="", help="Fallback bench_main binary if --gen-hpp omitted")
    ap.add_argument("--kissat", default="", help="Optional C1 kissat oracle for ground truth")
    ap.add_argument("--cnfs-dir", default="", help="Dir of .cnf inputs (e.g. pv_sat_bench/cnfs)")
    ap.add_argument("--max-cnfs", type=int, default=8, help="Max CNFs to sweep from --cnfs-dir")
    ap.add_argument("--max-work-bytes", type=int, default=8 * MiB, help="High work_cap bound")
    ap.add_argument("--fuel", type=int, default=20000000, help="Fuel per run")
    ap.add_argument("--timeout", type=int, default=10, help="Per-run timeout in seconds")
    ap.add_argument("--check-oom-monotone", action="store_true", help="Assert h->oom monotonicity")
    ap.add_argument("--test-oom-sticky", action="store_true", help="Probe h->oom stickiness")
    ap.add_argument("--check-inv", action="store_true", help="Enable -DKISSAT_C3B_CHECK_INV")
    ap.add_argument("--check-search-inv", action="store_true",
                    help="Check bins/2wl after full_search before full_extend")
    ap.add_argument("--fast", action="store_true", help="Use reduced fine-offset grid")
    ap.add_argument("--json-out", default="", help="Write full JSON report")
    args = ap.parse_args()

    if not args.gen_hpp and not args.c3b_bin:
        ap.error("pass either --gen-hpp or --c3b-bin")

    repo_root = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
    runtime_dir = os.path.join(repo_root, "LeanQbe", "T", "Runtime")
    verify_dir = os.path.dirname(os.path.abspath(__file__))
    offsets = FAST_FINE_OFFSETS if args.fast else DEFAULT_FINE_OFFSETS

    with tempfile.TemporaryDirectory(prefix="kissat-fuzz-oom-") as tmp_dir:
        if args.gen_hpp:
            use_inv = args.check_inv or args.check_search_inv
            driver = compile_driver(args.gen_hpp, tmp_dir, runtime_dir, verify_dir, use_inv)
            def invoke(cnf_p, wb, fl, to):
                return run_driver(driver, cnf_p, wb, fl, to, args.check_oom_monotone,
                                  args.check_inv, args.test_oom_sticky, args.check_search_inv)
        else:
            def invoke(cnf_p, wb, fl, to):
                return run_bench_cli(args.c3b_bin, cnf_p, wb, fl, to)

        cases = []
        if args.cnfs_dir:
            for p in sorted(glob.glob(os.path.join(args.cnfs_dir, "*.cnf")))[:args.max_cnfs]:
                base = os.path.basename(p)
                exp = "SAT" if "_sat_" in base else ("UNSAT" if "_unsat_" in base else "UNKNOWN")
                if args.kissat and os.path.exists(args.kissat):
                    exp = oracle_kissat(args.kissat, p, args.timeout)
                cases.append({"name": base, "path": p, "expected": exp})
        else:
            cases = gen_fuzz_corpus(tmp_dir)

        summary = {"cases": [], "totals": {
            "runs": 0, "flips": 0, "witness_check_fail": 0,
            "fuel_exhausted": 0, "oom_monotone_fail": 0, "inv_fail": 0, "crashes": 0,
        }}

        for case in cases:
            mv, _ = parse_dimacs_header(case["path"])
            base_rec = invoke(case["path"], args.max_work_bytes, args.fuel, args.timeout)
            min_solve = binary_search_min_cap(
                invoke, case["path"], 4096, args.max_work_bytes, args.fuel, args.timeout, True)
            min_parse = binary_search_min_cap(
                invoke, case["path"], 4096, min_solve, args.fuel, args.timeout, False)
            bounds = estimate_boundaries(mv, base_rec, args.max_work_bytes)
            bounds["min_parse"] = min_parse
            bounds["min_solve"] = min_solve

            sweep_caps = sorted({
                max(256, min(args.max_work_bytes, b + off))
                for b in bounds.values() for off in offsets
            })

            case_res = {
                "name": case["name"],
                "expected": case["expected"],
                "boundaries": bounds,
                "baseline_watermarks": {
                    k: base_rec.get(k, 0)
                    for k in ("arena_len", "arena_cap", "wlen", "wcap",
                              "extend_len", "extend_cap", "scratch_cap")
                },
                "sweeps": len(sweep_caps),
                "sat": 0, "unsat": 0, "fuel_exhausted": 0,
                "witness_check_fail": 0, "flips": 0, "oom_mono_fail": 0,
                "inv_fail": 0, "crashes": 0,
                "witness_fail_caps": [],
                "inv_err_samples": [],
            }
            for wb in sweep_caps:
                rec = invoke(case["path"], wb, args.fuel, args.timeout)
                summary["totals"]["runs"] += 1
                st = rec.get("status", -1)
                if rec.get("crash"):
                    case_res["crashes"] += 1
                    summary["totals"]["crashes"] += 1
                elif st == 3:
                    case_res["witness_check_fail"] += 1
                    summary["totals"]["witness_check_fail"] += 1
                    case_res["witness_fail_caps"].append(wb)
                elif st == 0:
                    case_res["fuel_exhausted"] += 1
                    summary["totals"]["fuel_exhausted"] += 1
                elif st == 10:
                    case_res["sat"] += 1
                    if case["expected"] == "UNSAT":
                        case_res["flips"] += 1
                        summary["totals"]["flips"] += 1
                elif st == 20:
                    case_res["unsat"] += 1
                    if case["expected"] == "SAT":
                        case_res["flips"] += 1
                        summary["totals"]["flips"] += 1
                if rec.get("oom_monotone_ok", 1) == 0:
                    case_res["oom_mono_fail"] += 1
                    summary["totals"]["oom_monotone_fail"] += 1
                if rec.get("inv_ok", 1) == 0:
                    case_res["inv_fail"] += 1
                    summary["totals"]["inv_fail"] += 1
                    if len(case_res["inv_err_samples"]) < 5:
                        case_res["inv_err_samples"].append(
                            {"work_bytes": wb, "err": rec.get("inv_err", "")}
                        )
            summary["cases"].append(case_res)
            print(
                f"{case['name']:<26} exp={case['expected']:<5} min={min_solve//1024:>4}K "
                f"sweeps={len(sweep_caps):>3} sat={case_res['sat']:>2} "
                f"unsat={case_res['unsat']:>2} fuel={case_res['fuel_exhausted']:>2} "
                f"WFAIL={case_res['witness_check_fail']:>2} flips={case_res['flips']} "
                f"oom_mono={case_res['oom_mono_fail']} inv_fail={case_res['inv_fail']}",
                flush=True,
            )

        if args.json_out:
            os.makedirs(os.path.dirname(os.path.abspath(args.json_out)), exist_ok=True)
            with open(args.json_out, "w", encoding="utf-8") as f:
                json.dump(summary, f, indent=2)

        t = summary["totals"]
        print(
            f"TOTAL runs={t['runs']} flips={t['flips']} "
            f"WITNESS_CHECK_FAIL={t['witness_check_fail']} "
            f"fuel_exhausted={t['fuel_exhausted']} oom_mono_fail={t['oom_monotone_fail']} "
            f"inv_fail={t['inv_fail']} crashes={t['crashes']}"
        )
        bad = (t["flips"] + t["witness_check_fail"] + t["oom_monotone_fail"]
               + t["inv_fail"] + t["crashes"])
        sys.exit(0 if bad == 0 else 1)


if __name__ == "__main__":
    main()
