#!/usr/bin/env python3
"""Run and check the 10-family tricky-UNSAT canary suite against baseline / Kissat 4.0.4.

Supports:
  - C4 native x64 binaries (`Full`, `FullFast`) via `bench_main.c --full-telemetry`
  - C3b `PrintCpp -DTQBE_NATIVE_MEM` binaries (`Full`, `FullFast`), asserting
    BIT-IDENTICAL `(status, conflicts, learned_lits, min_removed, search_ticks)` vs C4!
  - Optional upstream Kissat 4.0.4 (`--kissat <bin>`) comparison
  - Ratchet regression checks against `bench/kissat/canary_baseline.json` with
    explicit `expected_gap` tagging for known pre-M3 cliffs (no silent failures).
"""

import argparse
import json
import os
import re
import shlex
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True

INT_KEYS = {
    "conflicts", "learned_lits", "min_removed", "num_irred", "num_redundant",
    "num_binary", "switched", "search_ticks", "rephased", "reductions",
    "tier1", "tier2", "restarts", "oom", "max_vars", "cur_vars", "unassigned",
    "otfs", "eager_sub", "probings", "eliminations", "elim_bound",
    "hbr", "trans", "viv", "subst", "cong", "sweep", "bve", "bce", "bva",
    "walks", "fwd_sub", "fwd_str", "last_probe_ticks", "last_elim_ticks",
    "k_status", "k_conflicts", "k_decisions", "k_propagations", "k_reductions",
    "k_restarts", "k_viv", "k_subst", "k_cong", "k_sweep", "k_bve", "k_bva", "k_trans",
}
FLOAT_KEYS = {"k_ms"}
PARITY_KEYS = ("status", "conflicts", "learned_lits", "min_removed", "search_ticks")
KISSAT_STAT_MAP = {
    "conflicts": "k_conflicts",
    "decisions": "k_decisions",
    "propagations": "k_propagations",
    "reductions": "k_reductions",
    "restarts": "k_restarts",
    "vivified": "k_viv",
    "substituted": "k_subst",
    "congruent": "k_cong",
    "swept": "k_sweep",
    "eliminated": "k_bve",
    "factored": "k_bva",
    "transitive_reduced": "k_trans",
}


def parse_full_telemetry_line(line):
    parts = line.rstrip("\n").split("\t")
    if len(parts) < 4:
        raise RuntimeError(f"malformed telemetry line: {line!r}")
    rec = {
        "path": parts[0],
        "status": int(parts[1]),
        "ms": round(float(parts[2]), 3),
    }
    for tok in parts[3:]:
        if "=" not in tok:
            continue
        k, v = tok.split("=", 1)
        if k in INT_KEYS:
            rec[k] = int(v)
        elif k in FLOAT_KEYS:
            rec[k] = round(float(v), 3)
        else:
            rec[k] = v
    return rec


def run_one(bin_path, cnf_path, work_bytes, fuel, per_timeout, m2_alias=False, kissat_bin=None):
    cmd = ["timeout", str(per_timeout), bin_path,
           "--full-telemetry-m2" if m2_alias else "--full-telemetry"]
    if kissat_bin:
        cmd.extend(["--kissat", kissat_bin])
    cmd.extend([str(work_bytes), str(fuel), cnf_path])
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode == 124:
        return {"path": cnf_path, "status": -1, "timeout": True, "ms": float(per_timeout * 1000)}
    if proc.returncode != 0:
        raise RuntimeError(
            f"solver crashed ({proc.returncode}) on {cnf_path}:\n{proc.stderr}\n{proc.stdout}"
        )
    lines = [l for l in proc.stdout.splitlines() if l.strip()]
    if len(lines) != 1:
        raise RuntimeError(f"expected 1 telemetry line for {cnf_path}, got {len(lines)}")
    rec = parse_full_telemetry_line(lines[0])
    rec["timeout"] = False
    return rec


def run_kissat_one(kissat_bin, cnf_path, per_timeout, extra_flags=None):
    t0 = time.monotonic()
    cmd = ["timeout", str(per_timeout), kissat_bin, "-n", "-s"]
    if extra_flags:
        cmd.extend(extra_flags)
    cmd.append(cnf_path)
    proc = subprocess.run(cmd, capture_output=True, text=True)
    dt_ms = round((time.monotonic() - t0) * 1000.0, 3)
    if proc.returncode == 124:
        return {"k_status": -1, "k_timeout": True, "k_ms": float(per_timeout * 1000)}
    if proc.returncode not in (0, 10, 20):
        raise RuntimeError(
            f"kissat crashed ({proc.returncode}) on {cnf_path}:\n{proc.stderr}\n{proc.stdout}"
        )
    rec = {"k_status": proc.returncode, "k_timeout": False, "k_ms": dt_ms}
    for vkey in KISSAT_STAT_MAP.values():
        rec[vkey] = 0
    for line in proc.stdout.splitlines():
        if not line.startswith("c "):
            continue
        m = re.match(r"^c\s+([a-z_]+):\s+(\d+)\b", line)
        if m and m.group(1) in KISSAT_STAT_MAP:
            rec[KISSAT_STAT_MAP[m.group(1)]] = int(m.group(2))
    return rec


def compact_metrics(rec):
    keep = [
        "status", "timeout", "ms", "conflicts", "learned_lits", "min_removed",
        "search_ticks", "switched", "restarts", "reductions", "rephased", "oom",
        "otfs", "eager_sub", "probings", "eliminations", "elim_bound",
        "hbr", "trans", "viv", "subst", "cong", "sweep", "bve", "bce", "bva",
        "walks", "fwd_sub", "fwd_str", "last_probe_ticks", "last_elim_ticks",
        "k_status", "k_ms", "k_conflicts", "k_decisions", "k_propagations",
    ]
    return {k: rec[k] for k in keep if k in rec}


def check_parity(label, c4_rec, c3b_rec):
    if c4_rec.get("timeout") or c3b_rec.get("timeout"):
        return None
    diffs = []
    for k in PARITY_KEYS:
        if c4_rec.get(k) != c3b_rec.get(k):
            diffs.append(f"{k}: C4={c4_rec.get(k)} != C3b={c3b_rec.get(k)}")
    return diffs if diffs else None


def format_canary_status(rec):
    if rec.get("timeout"):
        return "TO"
    st = rec.get("status", -1)
    if st == 3:
        return "WFAIL"
    return str(st)


def evaluate_canary(entry, rec, baseline_rec=None, strict_gaps=False, kissat_rec=None):
    issues = []
    gaps = []
    fname = entry["file"]
    st = rec.get("status", -1)
    if st == 3:
        issues.append(f"WITNESS_CHECK_FAIL (status=3, oom={rec.get('oom', 0)}) on {fname}!")
    elif st == 10:
        issues.append(f"SOUNDNESS BUG: got SAT (10) on UNSAT canary {fname}!")
    elif st != 20:
        tag = "timeout" if rec.get("timeout") else "fuel_exhausted"
        msg = f"{tag} (status={st}, timeout={rec.get('timeout')}, oom={rec.get('oom', 0)})"
        if entry.get("expected_gap") and not strict_gaps:
            gaps.append(f"[{entry['expected_gap']}] {msg}")
        else:
            issues.append(msg)

    if rec.get("oom", 0) != 0:
        msg = f"oom={rec['oom']}"
        if entry.get("expected_gap") and not strict_gaps:
            gaps.append(f"[{entry['expected_gap']}] {msg}")
        else:
            issues.append(msg)

    if st == 20:
        for ck, lo in entry.get("min_counters", {}).items():
            got = rec.get(ck, 0)
            if ck == "oom":
                if got != 0:
                    issues.append(f"oom={got} != 0")
            elif got < lo:
                msg = f"counter {ck}={got} < {lo}"
                if entry.get("expected_gap") and not strict_gaps:
                    gaps.append(f"[{entry['expected_gap']}] {msg}")
                else:
                    issues.append(msg)
        any_map = entry.get("min_counters_any", {})
        if any_map and not any(rec.get(ck, 0) >= lo for ck, lo in any_map.items()):
            got_s = ", ".join(f"{ck}={rec.get(ck, 0)}" for ck in any_map)
            msg = f"none of {any_map} met ({got_s})"
            if entry.get("expected_gap") and not strict_gaps:
                gaps.append(f"[{entry['expected_gap']}] {msg}")
            else:
                issues.append(msg)

        kref = kissat_rec if kissat_rec is not None else rec
        if "k_conflicts" in kref and kref.get("k_status") == 20:
            kc = kref["k_conflicts"]
            c0c = rec.get("conflicts", 0)
            ceil = entry.get("kissat_confl_mult", 3.0) * kc + entry.get("kissat_confl_add", 500)
            if c0c > ceil:
                msg = f"c0_confl={c0c} > {ceil:.0f} (kissat={kc})"
                if entry.get("expected_gap") and not strict_gaps:
                    gaps.append(f"[{entry['expected_gap']}] {msg}")
                else:
                    issues.append(msg)

        if baseline_rec and baseline_rec.get("status") == 20:
            b_confl = baseline_rec.get("conflicts", 0)
            c_confl = rec.get("conflicts", 0)
            if c_confl > max(b_confl * 1.25 + 50, b_confl + 50):
                issues.append(f"conflict ratchet regression: {c_confl} > 1.25*{b_confl}+50")

    return issues, gaps


def fmt_median_ratio(vals):
    if not vals:
        return "n/a (n=0)"
    med = statistics.median(vals)
    return f"{med:.2f}x (n={len(vals)}, {min(vals):.2f}..{max(vals):.2f}x)"


def collect_c1_ratios(results, cfg_k, oracle_key="c1"):
    """Collect non-trivial time & conflict ratios vs C1/C2 on mutually solved cases."""
    matched = 0
    time_max10 = []
    time_both5 = []
    confl_k100 = []
    confl_both100 = []
    for r in results.values():
        m = r["runs"].get(cfg_k)
        k = r.get(oracle_key)
        if not m or not k:
            continue
        if m.get("status") != 20 or m.get("timeout"):
            continue
        if k.get("k_status") != 20 or k.get("k_timeout"):
            continue
        matched += 1
        mms = m.get("ms", 0.0)
        kms = k.get("k_ms", 0.0)
        if kms > 0.0:
            if max(mms, kms) >= 10.0:
                time_max10.append(mms / kms)
            if mms >= 5.0 and kms >= 5.0:
                time_both5.append(mms / kms)
        kc = k.get("k_conflicts", 0)
        mc = m.get("conflicts", 0)
        if kc >= 100:
            confl_k100.append(mc / kc)
            if mc >= 100:
                confl_both100.append(mc / kc)
    return matched, time_max10, time_both5, confl_k100, confl_both100


def collect_c2_vs_c1_ratios(results):
    """Collect algorithmic gap ratios C2 / C1 across mutually solved UNSAT canaries."""
    matched = 0
    time_max10 = []
    confl_k100 = []
    for r in results.values():
        c1 = r.get("c1")
        c2 = r.get("c2")
        if not c1 or not c2:
            continue
        if c1.get("k_status") != 20 or c1.get("k_timeout"):
            continue
        if c2.get("k_status") != 20 or c2.get("k_timeout"):
            continue
        matched += 1
        t1, t2 = c1.get("k_ms", 0.0), c2.get("k_ms", 0.0)
        if t1 > 0.0 and max(t1, t2) >= 10.0:
            time_max10.append(t2 / t1)
        k1, k2 = c1.get("k_conflicts", 0), c2.get("k_conflicts", 0)
        if k1 >= 100:
            confl_k100.append(k2 / k1)
    return matched, time_max10, confl_k100


C3B_HARNESS_CPP = r"""
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

#include "tqbe_rt.hpp"
#include "kissat_verify.h"

namespace tqbe_gen {
#include "__GEN_HPP__"
}

static uint64_t rd64(const void *p, size_t w) {
  uint64_t v = 0;
  std::memcpy(&v, static_cast<const uint8_t *>(p) + w * 8ULL, 8ULL);
  return v;
}

static void wr64(void *p, size_t w, uint64_t v) {
  std::memcpy(static_cast<uint8_t *>(p) + w * 8ULL, &v, 8ULL);
}

int main(int argc, char **argv) {
  if (argc < 4) return 2;
  int idx = 1;
  bool m2_alias = false;
  if (std::strcmp(argv[idx], "--full-telemetry-m2") == 0) {
    m2_alias = true;
    ++idx;
  } else if (std::strcmp(argv[idx], "--full-telemetry") == 0) {
    ++idx;
  }
  uint64_t work_bytes = std::strtoull(argv[idx], nullptr, 10);
  uint64_t fuel = std::strtoull(argv[idx + 1], nullptr, 10);
  const char *cnf_path = argv[idx + 2];
  FILE *f = std::fopen(cnf_path, "rb");
  if (!f) return 2;
  std::fseek(f, 0, SEEK_END);
  long sz = std::ftell(f);
  std::rewind(f);
  std::vector<uint8_t> cnf(sz > 0 ? static_cast<size_t>(sz) : 0);
  if (sz > 0 && std::fread(cnf.data(), 1, static_cast<size_t>(sz), f) != static_cast<size_t>(sz)) {
    std::fclose(f);
    return 2;
  }
  std::fclose(f);

  std::vector<uint8_t> work(static_cast<size_t>(work_bytes), 0);
  ::tqbe::Mem mem;
  uint64_t cnf_addr = reinterpret_cast<uint64_t>(cnf.data());
  uint64_t cnf_end = cnf_addr + static_cast<uint64_t>(cnf.size());
  uint64_t raw_ptr = reinterpret_cast<uint64_t>(work.data());
  uint64_t pad = (8ULL - (raw_ptr & 7ULL)) & 7ULL;
  uint64_t hdr_addr = raw_ptr + pad;
  uint64_t avail = work_bytes > pad ? (work_bytes - pad) : 0ULL;
  uint8_t *hp = work.data() + pad;

  auto t0 = std::chrono::steady_clock::now();
  bool ok = (avail >= 1152ULL) && tqbe_gen::full_init_state(
      mem, ::tqbe::bits<64>(cnf_addr), ::tqbe::bits<64>(cnf_end),
      ::tqbe::bits<64>(hdr_addr), ::tqbe::bits<64>(avail), ::tqbe::bits<64>(fuel));
  uint64_t st = 0;
  if (ok) {
    uint64_t orig_mv = rd64(hp, 0);
    uint64_t pb = tqbe_gen::full_parse_body(
        mem, ::tqbe::bits<64>(hdr_addr), ::tqbe::bits<64>(cnf_end)).data;
    if (pb != 1ULL) {
      st = pb;
    } else {
      uint64_t pp = tqbe_gen::full_preprocess(mem, ::tqbe::bits<64>(hdr_addr)).data;
      st = (pp == 1ULL) ? tqbe_gen::full_search(mem, ::tqbe::bits<64>(hdr_addr)).data : pp;
    }
    if (st == 10ULL) {
      tqbe_gen::full_extend(mem, ::tqbe::bits<64>(hdr_addr));
      wr64(hp, 0, orig_mv);
      wr64(hp, 98, rd64(hp, 96) - orig_mv);
      uint64_t vp = rd64(hp, 8);
      uint64_t chk = tqbe_gen::kissat_check_model(
          mem, ::tqbe::bits<64>(cnf_addr), ::tqbe::bits<64>(cnf_end),
          ::tqbe::bits<64>(hdr_addr), ::tqbe::bits<64>(vp), ::tqbe::bits<64>(orig_mv)).data;
      const int8_t *vals = reinterpret_cast<const int8_t *>(static_cast<uintptr_t>(vp));
      int d = kissat_verify_dimacs_model(
          reinterpret_cast<const char *>(cnf.data()), static_cast<uint64_t>(cnf.size()),
          vals, orig_mv);
      if (chk != 1ULL || d != 1) st = 3ULL;
    }
  }
  auto t1 = std::chrono::steady_clock::now();
  double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
  const void *h = hp;
  std::printf(
      "%s\t%llu\t%.3f\tconflicts=%llu\tlearned_lits=%llu\tmin_removed=%llu\t"
      "search_ticks=%llu\tswitched=%llu\trestarts=%llu\treductions=%llu\trephased=%llu\toom=%llu\t"
      "otfs=%llu\teager_sub=%llu\tprobings=%llu\teliminations=%llu\telim_bound=%llu\t"
      "hbr=%llu\ttrans=%llu\tviv=%llu\tsubst=%llu\tcong=%llu\tsweep=%llu\tbve=%llu\tbce=%llu\t"
      "bva=%llu\twalks=%llu\t%s\n",
      cnf_path, (unsigned long long)st, ms,
      (unsigned long long)(ok ? rd64(h, 42) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 43) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 44) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 75) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 70) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 89) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 86) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 84) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 95) : 1ULL),
      (unsigned long long)(ok ? rd64(h, 120) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 121) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 123) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 125) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 126) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 130) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 131) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 132) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 133) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 134) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 135) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 136) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 137) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 138) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 139) : 0ULL),
      m2_alias ? "last_probe_ticks=0\tlast_elim_ticks=0" : "fwd_sub=0\tfwd_str=0");
  return 0;
}
"""


def compile_c3b_gen_hpp(spec, tmp_dir):
    if "=" in spec:
        label, hpp = spec.split("=", 1)
    else:
        label, hpp = "FullM4_C3b", spec
    hpp_abs = os.path.abspath(hpp)
    bench_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.abspath(os.path.join(bench_dir, "..", ".."))
    cpp_path = os.path.join(tmp_dir, f"{label}_harness.cpp")
    bin_path = os.path.join(tmp_dir, f"{label}_harness")
    with open(cpp_path, "w", encoding="utf-8") as f:
        f.write(C3B_HARNESS_CPP.replace("__GEN_HPP__", hpp_abs))
    subprocess.run([
        "timeout", "180", "clang++", "-std=c++20", "-O3", "-DTQBE_NATIVE_MEM",
        f"-I{os.path.join(repo_root, 'LeanQbe', 'T', 'Runtime')}",
        f"-I{os.path.join(repo_root, 'test', 'kissat')}",
        f"-I{os.path.dirname(hpp_abs)}",
        cpp_path, "-o", bin_path,
    ], check=True)
    return label, bin_path


def main():
    ap = argparse.ArgumentParser(description="Run and verify 10-family Kissat UNSAT canaries.")
    ap.add_argument("--cnf-dir", help="Directory with generated canaries (auto-generated if omitted)")
    ap.add_argument("--full-c4", help="Path to C4 native x64 Full bench_main binary")
    ap.add_argument("--full-c3b", help="Path to C3b PrintCpp-native-mem Full bench_main binary")
    ap.add_argument("--fast-c4", help="Path to C4 native x64 FullFast bench_main binary")
    ap.add_argument("--fast-c3b", help="Path to C3b PrintCpp-native-mem FullFast bench_main binary")
    ap.add_argument("--m3-c4", help="Path to C4 native x64 FullM3 bench_main binary")
    ap.add_argument("--m3-c3b", help="Path to C3b PrintCpp-native-mem FullM3 bench_main binary")
    ap.add_argument("--m4-c4", help="Path to C4 native x64 FullM4 bench_main binary")
    ap.add_argument("--m4-c3b", help="Path to C3b PrintCpp-native-mem FullM4 bench_main binary")
    ap.add_argument("--kissat", help="Optional path to upstream Kissat 4.0.4 binary")
    ap.add_argument("--c2-flags", default="", help="Optional C2 flag-matched Kissat flags")
    ap.add_argument("--work-bytes", type=int, default=67108864, help="Workspace bytes (default 64 MiB)")
    ap.add_argument("--fuel", type=int, default=200000000, help="Solver fuel budget")
    ap.add_argument("--per-timeout", type=int, default=5, help="Per-CNF timeout in seconds (default 5)")
    ap.add_argument("--baseline", default="bench/kissat/canary_baseline.json", help="Baseline JSON path")
    ap.add_argument("--update-baseline", action="store_true", help="Write measured baseline JSON")
    ap.add_argument("--commit", default="", help="Git commit SHA to stamp into baseline JSON")
    ap.add_argument("--strict-gaps", action="store_true", help="Treat known pre-M3 gaps as hard failures")
    ap.add_argument("--filter", default="", help="Substring filter on canary filename")
    ap.add_argument(
        "--include-c11", action="store_true", help="Include 6 c11_* regression canaries",
    )
    ap.add_argument(
        "--c11-only", action="store_true", help="Run only the 6 c11_* regression canaries",
    )
    ap.add_argument(
        "--c3b-gen-hpp", action="append", default=[], metavar="LABEL=HPP",
        help="Compile witness-checking C3b harness from emitted *_gen.hpp",
    )
    args = ap.parse_args()

    if not any([
        args.full_c4, args.full_c3b, args.fast_c4, args.fast_c3b,
        args.m3_c4, args.m3_c3b, args.m4_c4, args.m4_c3b, args.c3b_gen_hpp,
    ]):
        ap.error(
            "specify at least one solver binary or --c3b-gen-hpp "
            "(--full-c4/--full-c3b/--fast-c4/--fast-c3b/--m3-c4/--m3-c3b/--m4-c4/--m4-c3b)"
        )

    kissat_bin = None
    if args.kissat:
        resolved = shutil.which(args.kissat) if os.sep not in args.kissat else args.kissat
        if not resolved or not os.path.isfile(resolved) or not os.access(resolved, os.X_OK):
            ap.error(f"--kissat binary not executable: {args.kissat}")
        kissat_bin = resolved

    tmp_ctx = None
    cnf_dir = args.cnf_dir
    if not cnf_dir:
        tmp_ctx = tempfile.TemporaryDirectory(prefix="kissat-canaries-")
        cnf_dir = tmp_ctx.name
        gen_script = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen_canary_cnfs.py")
        gen_cmd = ["timeout", "60", sys.executable, "-B", gen_script, cnf_dir]
        if args.c11_only:
            gen_cmd.append("--c11-only")
        elif args.include_c11:
            gen_cmd.append("--include-c11")
        subprocess.run(gen_cmd, check=True)

    with open(os.path.join(cnf_dir, "manifest.json"), encoding="utf-8") as f:
        manifest = json.load(f)["canaries"]
    if args.c11_only:
        manifest = [e for e in manifest if e["file"].startswith("c11_")]
    elif not args.include_c11:
        manifest = [e for e in manifest if not e["file"].startswith("c11_")]
    if args.filter:
        manifest = [e for e in manifest if args.filter in e["file"]]

    baseline = None
    if not args.update_baseline and os.path.exists(args.baseline):
        with open(args.baseline, encoding="utf-8") as f:
            baseline = json.load(f)

    c3b_tmp_ctx = None
    configs = []
    if args.full_c4:
        configs.append(("Full_C4", args.full_c4, False))
    if args.full_c3b:
        configs.append(("Full_C3b", args.full_c3b, False))
    if args.fast_c4:
        configs.append(("FullFast_C4", args.fast_c4, True))
    if args.fast_c3b:
        configs.append(("FullFast_C3b", args.fast_c3b, True))
    if args.m3_c4:
        configs.append(("FullM3_C4", args.m3_c4, True))
    if args.m3_c3b:
        configs.append(("FullM3_C3b", args.m3_c3b, True))
    if args.m4_c4:
        configs.append(("FullM4_C4", args.m4_c4, True))
    if args.m4_c3b:
        configs.append(("FullM4_C3b", args.m4_c3b, True))
    if args.c3b_gen_hpp:
        c3b_tmp_ctx = tempfile.TemporaryDirectory(prefix="kissat-c3b-harness-")
        for spec in args.c3b_gen_hpp:
            label, bpath = compile_c3b_gen_hpp(spec, c3b_tmp_ctx.name)
            configs.append((label, bpath, True))

    results = {}
    hard_fails = []
    parity_fails = []
    all_gaps = []

    hdr = (
        f"{'Canary':<28} {'Cfg':<12} {'St':>3} {'ms':>8} {'Confl':>8} "
        f"{'Ticks':>10} {'BVA':>4} {'Cong':>4} {'Swp':>4} {'Viv':>4} {'BVE':>4} {'Trns':>5} {'Red':>4}"
    )
    c2_flags = shlex.split(args.c2_flags) if args.c2_flags else []
    if kissat_bin:
        hdr += f" | {'K_St':>4} {'K_ms':>8} {'K_confl':>8}"
        if c2_flags:
            hdr += f" | {'C2_St':>5} {'C2_ms':>8} {'C2_cnfl':>8}"
    print(hdr)
    print("-" * len(hdr))

    for entry in manifest:
        fname = entry["file"]
        cpath = os.path.join(cnf_dir, fname)
        row = {"family": entry["family"], "expected_gap": entry.get("expected_gap", ""), "runs": {}}
        k_rec = run_kissat_one(kissat_bin, cpath, args.per_timeout) if kissat_bin else None
        c2_rec = (
            run_kissat_one(kissat_bin, cpath, args.per_timeout, c2_flags)
            if (kissat_bin and c2_flags) else None
        )
        if k_rec is not None:
            row["c1"] = k_rec
            if k_rec.get("k_status") == 10:
                hard_fails.append(
                    f"{fname} [C1]: SOUNDNESS BUG: got SAT (10) on UNSAT canary {fname}!"
                )
        if c2_rec is not None:
            row["c2"] = c2_rec
            if c2_rec.get("k_status") == 10:
                hard_fails.append(
                    f"{fname} [C2]: SOUNDNESS BUG: got SAT (10) on UNSAT canary {fname}!"
                )

        for name, bpath, is_m2 in configs:
            rec = run_one(bpath, cpath, args.work_bytes, args.fuel, args.per_timeout, is_m2)
            row["runs"][name] = compact_metrics(rec)
            st_s = format_canary_status(rec)
            line = (
                f"{fname:<28} {name:<12} {st_s:>3} {rec['ms']:>8.2f} "
                f"{rec.get('conflicts', 0):>8} {rec.get('search_ticks', 0):>10} "
                f"{rec.get('bva', 0):>4} {rec.get('cong', 0):>4} {rec.get('sweep', 0):>4} "
                f"{rec.get('viv', 0):>4} {rec.get('bve', 0):>4} {rec.get('trans', 0):>5} "
                f"{rec.get('reductions', 0):>4}"
            )
            if k_rec is not None:
                kst_s = "TO" if k_rec.get("k_timeout") else str(k_rec.get("k_status", -1))
                kcf_s = "-" if k_rec.get("k_timeout") else str(k_rec.get("k_conflicts", 0))
                line += f" | {kst_s:>4} {k_rec['k_ms']:>8.2f} {kcf_s:>8}"
                if c2_rec is not None:
                    c2s = "TO" if c2_rec.get("k_timeout") else str(c2_rec.get("k_status", -1))
                    c2c = "-" if c2_rec.get("k_timeout") else str(c2_rec.get("k_conflicts", 0))
                    line += f" | {c2s:>5} {c2_rec['k_ms']:>8.2f} {c2c:>8}"
            print(line)
            base_rec = None
            if baseline and fname in baseline.get("canaries", {}):
                base_runs = baseline["canaries"][fname].get("runs", {})
                base_rec = base_runs.get(name)
                if base_rec is None and name.startswith("FullM4_"):
                    base_rec = base_runs.get(name.replace("FullM4_", "FullM3_", 1))
            issues, gaps = evaluate_canary(entry, rec, base_rec, args.strict_gaps, kissat_rec=k_rec)
            for msg in issues:
                hard_fails.append(f"{fname} [{name}]: {msg}")
            for msg in gaps:
                all_gaps.append(f"{fname} [{name}]: {msg}")

        # Bit-identical work parity check: C4 == C3b
        for base_mod in ("Full", "FullFast", "FullM3", "FullM4"):
            c4_k, c3b_k = f"{base_mod}_C4", f"{base_mod}_C3b"
            if c4_k in row["runs"] and c3b_k in row["runs"]:
                diffs = check_parity(base_mod, row["runs"][c4_k], row["runs"][c3b_k])
                if diffs:
                    parity_fails.append(f"{fname} [{base_mod} C4 vs C3b]: " + "; ".join(diffs))

        results[fname] = row

    tot = len(results)
    print("\n== Canary Summary ==")
    for name, _, _ in configs:
        solved = sum(1 for r in results.values() if r["runs"][name].get("status") == 20)
        wfail = sum(1 for r in results.values() if r["runs"][name].get("status") == 3)
        tot_ms = sum(r["runs"][name]["ms"] for r in results.values())
        extra = f", WFAIL={wfail}" if wfail else ""
        print(f"  {name:<14}: {solved:2d}/{tot} UNSAT solved{extra}  (total {tot_ms:.1f} ms)")

    for base_mod in ("Full", "FullFast", "FullM3", "FullM4"):
        c4_k, c3b_k = f"{base_mod}_C4", f"{base_mod}_C3b"
        if any(c4_k in r["runs"] and c3b_k in r["runs"] for r in results.values()):
            matched = 0
            ratios = []
            for r in results.values():
                a, b = r["runs"][c4_k], r["runs"][c3b_k]
                if not a.get("timeout") and not b.get("timeout"):
                    matched += 1
                    if b["ms"] > 0.5 and a["ms"] > 0.5:
                        ratios.append(a["ms"] / b["ms"])
            med = sorted(ratios)[len(ratios) // 2] if ratios else 0.0
            print(
                f"  C4/C3b parity [{base_mod}]: {matched} non-timeout matched"
                f" ({len([x for x in parity_fails if base_mod in x])} mismatches),"
                f" median C4/C3b time ratio = {med:.2f}x"
            )

    if kissat_bin:
        c1_solved = sum(1 for r in results.values() if r["c1"].get("k_status") == 20)
        c1_tot_ms = sum(r["c1"].get("k_ms", 0.0) for r in results.values())
        c1_solved_ms = sum(
            r["c1"].get("k_ms", 0.0) for r in results.values() if r["c1"].get("k_status") == 20
        )
        print("\n== C1 (Upstream Kissat) Comparison ==")
        print(
            f"  C1 (Kissat)   : {c1_solved:2d}/{tot} UNSAT solved"
            f"  (total {c1_tot_ms:.1f} ms, solved-only {c1_solved_ms:.1f} ms)"
        )
        for base_mod in ("Full", "FullFast", "FullM3", "FullM4"):
            c3b_k, c4_k = f"{base_mod}_C3b", f"{base_mod}_C4"
            has_c3b = any(c3b_k in r["runs"] for r in results.values())
            has_c4 = any(c4_k in r["runs"] for r in results.values())
            if not (has_c3b or has_c4):
                continue
            ref_k = c3b_k if has_c3b else c4_k
            matched, _, _, confl_k100, confl_both100 = collect_c1_ratios(results, ref_k)
            mod_solved = sum(1 for r in results.values() if r["runs"][ref_k].get("status") == 20)
            print(
                f"  [{base_mod}] matched solved vs C1: {matched}"
                f"  (module {mod_solved}/{tot}, C1 {c1_solved}/{tot})"
            )
            if has_c3b:
                _, t_max10, t_both5, _, _ = collect_c1_ratios(results, c3b_k)
                print(
                    f"    C3b/C1 time   (max>=10ms): median={fmt_median_ratio(t_max10)}"
                    f"  | (both>=5ms): median={fmt_median_ratio(t_both5)}"
                )
            if has_c4:
                _, t_max10, t_both5, _, _ = collect_c1_ratios(results, c4_k)
                print(
                    f"    C4 /C1 time   (max>=10ms): median={fmt_median_ratio(t_max10)}"
                    f"  | (both>=5ms): median={fmt_median_ratio(t_both5)}"
                )
            print(
                f"    confl/C1 ratio (K>=100)  : median={fmt_median_ratio(confl_k100)}"
                f"  | (both>=100): median={fmt_median_ratio(confl_both100)}"
            )
            if c2_flags:
                c2_m, c2_t, c2_c = collect_c2_vs_c1_ratios(results)
                print(
                    f"    [C2/C1 Algorithmic Gap]  : matched={c2_m}, "
                    f"time(max>=10ms)={fmt_median_ratio(c2_t)}, "
                    f"confl(K>=100)={fmt_median_ratio(c2_c)}"
                )
                if has_c3b:
                    m32, t32, _, c32, _ = collect_c1_ratios(results, c3b_k, oracle_key="c2")
                    print(
                        f"    [C3b/C2 Port/Layout Gap] : matched={m32}, "
                        f"time(max>=10ms)={fmt_median_ratio(t32)}, "
                        f"confl(C2>=100)={fmt_median_ratio(c32)}"
                    )

    if all_gaps:
        print(f"\nKnown pre-M3 gaps observed ({len(all_gaps)}):")
        for g in all_gaps[:25]:
            print(f"  GAP: {g}")
        if len(all_gaps) > 25:
            print(f"  ... ({len(all_gaps) - 25} more)")

    if args.update_baseline:
        out_doc = {
            "schema_version": 1,
            "base_commit": args.commit,
            "work_bytes": args.work_bytes,
            "fuel": args.fuel,
            "per_timeout_sec": args.per_timeout,
            "configs": [c[0] for c in configs],
            "canaries": results,
        }
        with open(args.baseline, "w", encoding="utf-8") as f:
            json.dump(out_doc, f, indent=2)
            f.write("\n")
        print(f"\nWrote baseline to {args.baseline}")

    if tmp_ctx is not None:
        tmp_ctx.cleanup()
    if c3b_tmp_ctx is not None:
        c3b_tmp_ctx.cleanup()

    if parity_fails:
        print("\nFAIL: C4 vs C3b bit-identical work parity mismatch:", file=sys.stderr)
        for p in parity_fails:
            print("  " + p, file=sys.stderr)
        sys.exit(1)

    if hard_fails:
        print("\nFAIL: Canary gate failures:", file=sys.stderr)
        for fmsg in hard_fails:
            print("  " + fmsg, file=sys.stderr)
        sys.exit(1)

    print("\nPASS: Zero soundness bugs, zero C4/C3b parity mismatches, zero ratchet regressions.")


if __name__ == "__main__":
    main()
