#!/usr/bin/env python3
"""Matched C1 vs C3b telemetry differential harness & CI drift alarm detector.

Runs upstream Kissat C1 (--verbose) and LeanQbe Kissat C3b across Canaries,
PV-35, or Hard-24/custom CNF suites, computing per-instance and aggregate C3b/C1
metric ratios, headroom watermarks, and CI drift alarms.
"""

import argparse
import glob
import json
import math
import os
import re
import shlex
import subprocess
import sys
import tempfile
import time

from diff_lockstep import prepare_c3b_wrapped_hpp

TELEM_METRICS = [
    "conflicts", "decisions", "search_ticks", "propagations", "restarts",
    "switched", "reductions", "vivified", "eliminated", "substituted",
    "congruent", "swept", "factored", "otfs", "hbr", "compactions",
    "chrono_bt_cnt", "kitten_calls", "backbone_units", "reduced_clauses",
    "probe_ticks", "elim_ticks", "vivify_ticks", "sweep_ticks",
    "cong_ticks", "factor_ticks",
]
INPROC_METRICS = [
    "vivified", "eliminated", "substituted", "congruent", "swept", "factored",
]
EXT_KEYS = [
    "decisions", "propagations", "chrono_bt_cnt", "kitten_calls",
    "kitten_ticks", "backbone_units", "reduced_clauses",
    "probe_ticks", "probe_wall_ns", "elim_ticks", "elim_wall_ns",
    "vivify_ticks", "vivify_wall_ns", "sweep_ticks", "sweep_wall_ns",
    "cong_ticks", "cong_wall_ns", "factor_ticks", "factor_wall_ns",
    "subst_wall_ns", "trans_wall_ns", "backbone_wall_ns",
    "fwd_sub_wall_ns", "compact_cnt", "compact_wall_ns",
    "otfs_subsume", "restarts_reused_levels",
    "stable_decisions", "focused_decisions", "probe_calls", "vivify_calls",
]
C1_STAT_ALIASES = {
    "conflicts": ("conflicts",),
    "decisions": ("decisions",),
    "search_ticks": ("search_ticks",),
    "propagations": ("propagations",),
    "restarts": ("restarts",),
    "switched": ("switched",),
    "reductions": ("reductions",),
    "vivified": ("vivified",),
    "eliminated": ("eliminated",),
    "substituted": ("substituted",),
    "congruent": ("congruent",),
    "swept": ("sweep_equivalences", "sweep_units"),
    "factored": ("factored",),
    "otfs": ("on_the_fly_strengthened",),
    "hbr": ("hyper_binary_resolved",),
    "compactions": ("compacted",),
    "chrono_bt_cnt": ("chronological",),
    "kitten_calls": ("kitten_solved",),
    "backbone_units": ("backbone_units",),
    "reduced_clauses": ("clauses_reduced",),
    "probe_ticks": ("probing_ticks",),
    "factor_ticks": ("factor_ticks",),
}

C3B_TELEM_CPP = r"""
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
  uint64_t x = 0;
  std::memcpy(&x, static_cast<const uint8_t *>(p) + w * 8ULL, 8ULL);
  return x;
}

static void wr64(void *p, size_t w, uint64_t v) {
  std::memcpy(static_cast<uint8_t *>(p) + w * 8ULL, &v, 8ULL);
}

int main(int argc, char **argv) {
  if (argc < 2) return 2;
  uint64_t work_bytes = 32ULL * 1024ULL * 1024ULL;
  uint64_t fuel = 50000000ULL;
  for (int i = 2; i < argc; ++i) {
    if (std::strncmp(argv[i], "--work-bytes=", 13) == 0) {
      work_bytes = std::strtoull(argv[i] + 13, nullptr, 10);
    } else if (std::strncmp(argv[i], "--fuel=", 7) == 0) {
      fuel = std::strtoull(argv[i] + 7, nullptr, 10);
    }
  }
  FILE *f = std::fopen(argv[1], "rb");
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
      uint64_t c = tqbe_gen::kissat_check_model(
          mem, ::tqbe::bits<64>(cnf_addr), ::tqbe::bits<64>(cnf_end),
          ::tqbe::bits<64>(hdr_addr), ::tqbe::bits<64>(vp), ::tqbe::bits<64>(orig_mv)).data;
      const int8_t *vals = reinterpret_cast<const int8_t *>(static_cast<uintptr_t>(vp));
      int d = kissat_verify_dimacs_model(
          reinterpret_cast<const char *>(cnf.data()), static_cast<uint64_t>(cnf.size()),
          vals, orig_mv);
      if (c != 1ULL || d != 1) st = 3ULL;
    }
  }
  auto t1 = std::chrono::steady_clock::now();
  double ms = std::chrono::duration<double, std::milli>(t1 - t0).count();
  const void *h = hp;
  uint64_t ext[32]{};
  bool has_ext = false;
  uint64_t del_addr = ok ? rd64(h, 16) : 0ULL;
  uint64_t del_cap = ok ? rd64(h, 56) : 0ULL;
  if (del_addr && del_cap >= 22ULL) {
    std::memcpy(ext, reinterpret_cast<const void *>(static_cast<uintptr_t>(del_addr)), sizeof(ext));
    has_ext = (ext[0] == 0x4B54454C4D303031ULL);
  }
  std::printf(
      "{\"status\":%llu,\"ms\":%.3f,\"oom\":%llu,"
      "\"conflicts\":%llu,\"search_ticks\":%llu,\"restarts\":%llu,\"switched\":%llu,"
      "\"reductions\":%llu,\"vivified\":%llu,\"eliminated\":%llu,\"substituted\":%llu,"
      "\"congruent\":%llu,\"swept\":%llu,\"factored\":%llu,\"otfs\":%llu,\"hbr\":%llu,"
      "\"arena_len\":%llu,\"arena_cap\":%llu,\"wlen\":%llu,\"wcap\":%llu,"
      "\"extend_len\":%llu,\"extend_cap\":%llu,\"scratch_cap\":%llu",
      (unsigned long long)st, ms,
      (unsigned long long)(ok ? rd64(h, 95) : 1ULL),
      (unsigned long long)(ok ? rd64(h, 42) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 75) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 89) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 70) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 86) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 132) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 136) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 133) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 134) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 135) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 138) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 120) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 130) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 6) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 4) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 7) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 5) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 114) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 113) : 0ULL),
      (unsigned long long)(ok ? rd64(h, 116) : 0ULL));
  if (has_ext) {
    static const char *const kNames[31] = {
        "decisions", "propagations", "chrono_bt_cnt", "kitten_calls",
        "kitten_ticks", "backbone_units", "reduced_clauses",
        "probe_ticks", "probe_wall_ns", "elim_ticks", "elim_wall_ns",
        "vivify_ticks", "vivify_wall_ns", "sweep_ticks", "sweep_wall_ns",
        "cong_ticks", "cong_wall_ns", "factor_ticks", "factor_wall_ns",
        "subst_wall_ns", "trans_wall_ns", "backbone_wall_ns",
        "fwd_sub_wall_ns", "compact_cnt", "compact_wall_ns",
        "otfs_subsume", "restarts_reused_levels",
        "stable_decisions", "focused_decisions", "probe_calls", "vivify_calls"};
    for (int j = 0; j < 31; ++j) {
      std::printf(",\"%s\":%llu", kNames[j], (unsigned long long)ext[j + 1]);
    }
  }
  std::printf("}\n");
  return 0;
}
"""


def compile_c3b_runner(gen_hpp, tmp_dir, repo_root, ext_telem=False):
    """Build C3b FullHdr (and optional extended) telemetry binary."""
    hpp_abs = os.path.abspath(gen_hpp)
    use_hpp = hpp_abs
    if ext_telem:
        use_hpp = os.path.join(tmp_dir, "c3b_telem_wrapped.hpp")
        prepare_c3b_wrapped_hpp(hpp_abs, use_hpp)
    cpp_path = os.path.join(tmp_dir, "c3b_telem.cpp")
    bin_path = os.path.join(tmp_dir, "c3b_telem")
    with open(cpp_path, "w", encoding="utf-8") as f:
        f.write(C3B_TELEM_CPP.replace("__GEN_HPP__", use_hpp))
    cmd = [
        "timeout", "180", "clang++", "-std=c++20", "-O3",
        "-Wall", "-Wextra", "-Werror", "-DTQBE_NATIVE_MEM",
        f"-I{os.path.join(repo_root, 'LeanQbe', 'T', 'Runtime')}",
        f"-I{os.path.join(repo_root, 'test', 'kissat')}",
        f"-I{os.path.join(repo_root, 'bench', 'kissat')}",
        f"-I{os.path.dirname(use_hpp)}",
        f"-I{os.path.dirname(hpp_abs)}",
    ]
    if ext_telem:
        cmd.append("-DKISSAT_EXTENDED_TELEM")
    cmd.extend([cpp_path, "-o", bin_path])
    subprocess.run(cmd, check=True)
    return bin_path


def run_c1(kissat_bin, cnf_path, timeout_s):
    """Run upstream Kissat with --verbose and extract telemetry counters."""
    t0 = time.monotonic()
    proc = subprocess.run(
        ["timeout", str(timeout_s), kissat_bin, "-n", "--verbose=1", cnf_path],
        capture_output=True, text=True,
    )
    ms = (time.monotonic() - t0) * 1000.0
    raw = {}
    for line in proc.stdout.splitlines():
        m = re.match(r"^c\s+([a-z0-9_]+):\s+(\d+)\b", line)
        if m:
            raw[m.group(1)] = int(m.group(2))
    out = {
        "status": 0 if proc.returncode == 124 else proc.returncode,
        "timeout": proc.returncode == 124,
        "ms": round(ms, 3),
    }
    for k, aliases in C1_STAT_ALIASES.items():
        present = [raw[a] for a in aliases if a in raw]
        out[k] = sum(present) if present else None
    return out


def run_c3b_runner(bin_path, cnf_path, work_bytes, fuel, timeout_s):
    """Run compiled C3b telemetry driver and return metric dict."""
    proc = subprocess.run(
        ["timeout", str(timeout_s), bin_path, cnf_path,
         f"--work-bytes={work_bytes}", f"--fuel={fuel}"],
        capture_output=True, text=True,
    )
    if proc.returncode == 124:
        return {"status": 0, "timeout": True, "ms": timeout_s * 1000.0}
    if proc.returncode != 0:
        return {"status": -1, "timeout": False, "crash": True, "ms": 0.0}
    for line in proc.stdout.splitlines():
        if line.strip().startswith("{"):
            rec = json.loads(line.strip())
            rec["timeout"] = False
            rec.setdefault("propagations", None)
            rec.setdefault("compactions", None)
            return rec
    return {"status": -1, "timeout": False, "crash": True, "ms": 0.0}


def run_c3b_cli(c3b_bin, cnf_path, work_bytes, fuel, timeout_s, ext_telem=False):
    """Fallback telemetry runner using bench_main --full/extended-telemetry-m2."""
    t0 = time.monotonic()
    flag = "--extended-telemetry-m2" if ext_telem else "--full-telemetry-m2"
    proc = subprocess.run(
        ["timeout", str(timeout_s), c3b_bin, flag,
         str(work_bytes), str(fuel), cnf_path],
        capture_output=True, text=True,
    )
    ms = (time.monotonic() - t0) * 1000.0
    rec = {"status": 0 if proc.returncode == 124 else proc.returncode,
           "timeout": proc.returncode == 124, "ms": round(ms, 3),
           "propagations": None, "compactions": None, "factored": None}
    lines = [l.strip() for l in proc.stdout.splitlines() if l.strip()]
    if lines and "\t" in lines[0]:
        parts = lines[0].split("\t")
        if len(parts) >= 3 and parts[1].isdigit():
            rec["status"] = int(parts[1])
            rec["ms"] = round(float(parts[2]), 3)
            remap = {
                "conflicts": "conflicts", "search_ticks": "search_ticks",
                "restarts": "restarts", "switched": "switched",
                "reductions": "reductions", "viv": "vivified", "bve": "eliminated",
                "subst": "substituted", "cong": "congruent", "sweep": "swept",
                "bva": "factored", "otfs": "otfs", "hbr": "hbr", "oom": "oom",
            }
            for ek in EXT_KEYS:
                remap[ek] = ek
            for tok in parts[3:]:
                if "=" in tok:
                    k, v = tok.split("=", 1)
                    if k in remap and v.isdigit():
                        rec[remap[k]] = int(v)
    return rec


def detect_alarms(c1, c3b, inproc_min_c1, ticks_min_confl):
    """Evaluate §5 CI drift alarms and headroom watermarks for one benchmark."""
    alarms = []
    watermarks = {}
    for num_k, den_k, label, thr in [
        ("extend_len", "extend_cap", "extend", 0.75),
        ("wlen", "wcap", "watch", 0.90),
        ("arena_len", "arena_cap", "arena", 0.90),
    ]:
        num, den = c3b.get(num_k), c3b.get(den_k)
        if isinstance(num, int) and isinstance(den, int) and den > 0:
            ratio = num / den
            watermarks[label] = round(ratio, 4)
            if ratio > thr:
                alarms.append(f"{label}_headroom({num}/{den}={ratio:.2%}>{thr:.0%})")
        else:
            watermarks[label] = None

    if c3b.get("status") == 3:
        alarms.append("WITNESS_CHECK_FAIL(status=3)")
    elif c1.get("status") in (10, 20) and c3b.get("status") in (10, 20):
        if c1["status"] != c3b["status"]:
            alarms.append(f"VERDICT_MISMATCH(C1={c1['status']},C3b={c3b['status']})")
    if c3b.get("oom", 0):
        alarms.append("C3B_OOM")

    for k in INPROC_METRICS:
        v1, v3 = c1.get(k), c3b.get(k)
        if v1 is not None and v3 is not None and v1 >= inproc_min_c1:
            if v3 == 0 or (v1 / v3) > 5.0:
                alarms.append(f"inproc_collapse:{k}(C1={v1},C3b={v3})")

    c1_c, c3_c = c1.get("conflicts"), c3b.get("conflicts")
    c1_t, c3_t = c1.get("search_ticks"), c3b.get("search_ticks")
    if (c1_c and c3_c and c1_c >= ticks_min_confl and c3_c >= ticks_min_confl
            and c1_t and c3_t):
        tpc1 = c1_t / c1_c
        tpc3 = c3_t / c3_c
        div = tpc3 / tpc1 if tpc1 > 0 else float("inf")
        if div > 2.5 or (div > 0 and (1.0 / div) > 2.5):
            alarms.append(f"ticks_per_confl_div(C1={tpc1:.1f},C3b={tpc3:.1f},x={div:.2f})")

    return watermarks, alarms


def load_benchmarks(args, tmp_dir, bench_dir):
    """Collect benchmark entries for Canaries, PV-35, Hard-24, or CNF directory."""
    cases = []
    if args.pv35_manifest:
        mdir = os.path.dirname(os.path.abspath(args.pv35_manifest))
        with open(args.pv35_manifest, "r", encoding="utf-8") as f:
            data = json.load(f)
        for e in data.get("benchmarks", data if isinstance(data, list) else []):
            p = os.path.join(mdir, e["cnf_relpath"]) if "cnf_relpath" in e else e["path"]
            cases.append({
                "name": e.get("name", os.path.basename(p)),
                "path": p,
                "work_bytes": int(e.get("min_work_mb", 32)) * 1024 * 1024,
            })
    elif args.cnf_dir:
        for p in sorted(glob.glob(os.path.join(args.cnf_dir, "*.cnf"))):
            cases.append({"name": os.path.basename(p), "path": p, "work_bytes": args.work_bytes})
    else:
        gen_cmd = ["timeout", "60", sys.executable, "-B",
                   os.path.join(bench_dir, "gen_canary_cnfs.py"), tmp_dir]
        if args.include_c11:
            gen_cmd.append("--include-c11")
        subprocess.run(gen_cmd, check=True)
        with open(os.path.join(tmp_dir, "manifest.json"), "r", encoding="utf-8") as f:
            man = json.load(f)
        for e in man["canaries"]:
            cases.append({
                "name": e["file"],
                "path": os.path.join(tmp_dir, e["file"]),
                "work_bytes": args.work_bytes,
            })
    if args.filter:
        cases = [c for c in cases if args.filter in c["name"]]
    if args.max_cases > 0:
        cases = cases[:args.max_cases]
    return cases


def fmt_ratio(c1_v, c3b_v):
    """Format C3b / C1 ratio cell concisely."""
    if c1_v is None or c3b_v is None:
        return "n/a"
    if c1_v == 0 and c3b_v == 0:
        return "1.00x (0/0)"
    if c1_v == 0:
        return f"inf ({c3b_v}/0)"
    return f"{c3b_v / c1_v:.2f}x ({c3b_v}/{c1_v})"


def build_markdown(results, agg_ratios):
    """Render Markdown telemetry ratio & watermark report."""
    lines = [
        "# C3b vs C1 Matched Telemetry Report",
        "",
        "| Case | St(C1/C3b) | Confl(C3b/C1) | Ticks(C3b/C1) | ExtLen/Cap | WLen/Cap "
        "| ArenaLen/Cap | Alarms |",
        "|---|---|---:|---:|---:|---:|---:|---|",
    ]
    for r in results:
        c1, c3, wm = r["c1"], r["c3b"], r["watermarks"]
        ext = f"{wm['extend']:.2f}" if wm["extend"] is not None else "n/a"
        wl = f"{wm['watch']:.2f}" if wm["watch"] is not None else "n/a"
        ar = f"{wm['arena']:.2f}" if wm["arena"] is not None else "n/a"
        al = ", ".join(r["alarms"]) if r["alarms"] else "-"
        lines.append(
            f"| {r['name']} | {c1['status']}/{c3['status']} "
            f"| {fmt_ratio(c1.get('conflicts'), c3.get('conflicts'))} "
            f"| {fmt_ratio(c1.get('search_ticks'), c3.get('search_ticks'))} "
            f"| {ext} | {wl} | {ar} | {al} |"
        )
    lines.extend(["", "## Aggregate C3b / C1 Metric Summary", "",
                  "| Metric | Cases | Sum C1 | Sum C3b | Aggregate Ratio |",
                  "|---|---:|---:|---:|---:|"])
    for m in TELEM_METRICS:
        s = agg_ratios[m]
        lines.append(f"| {m} | {s['cases']} | {s['sum_c1']} | {s['sum_c3b']} | {s['ratio']} |")
    return "\n".join(lines) + "\n"


def main():
    ap = argparse.ArgumentParser(description="Differential telemetry C1 vs C3b with CI alarms.")
    ap.add_argument("--kissat", required=True, help="Upstream Kissat C1 binary")
    ap.add_argument("--gen-hpp", default="", help="C3b emitted *_gen.hpp for full FullHdr metrics")
    ap.add_argument("--c3b-bin", default="", help="Fallback bench_main binary if --gen-hpp omitted")
    ap.add_argument("--pv35-manifest", default="", help="PV-35 / Hard-24 manifest JSON")
    ap.add_argument("--cnf-dir", default="", help="Custom directory of .cnf files")
    ap.add_argument("--include-c11", action="store_true", help="Include c11_* regression canaries")
    ap.add_argument("--filter", default="", help="Substring filter on benchmark name")
    ap.add_argument("--max-cases", type=int, default=0, help="Limit number of benchmarks")
    ap.add_argument("--work-bytes", type=int, default=32 * 1024 * 1024, help="Default C3b work_cap")
    ap.add_argument("--fuel", type=int, default=50000000, help="C3b fuel limit")
    ap.add_argument("--timeout", type=int, default=15, help="Per-solver timeout (seconds)")
    ap.add_argument("--inproc-min-c1", type=int, default=5, help="Min C1 count for 5x collapse")
    ap.add_argument("--ticks-min-confl", type=int, default=10, help="Min conflicts for ticks/confl")
    ap.add_argument("--extended-telemetry", action="store_true",
                    help="Collect §3 Layer 2 extended per-pass counters via h->delayed")
    ap.add_argument("--json-out", default="", help="Output JSON report path")
    ap.add_argument("--md-out", default="", help="Output Markdown table path")
    ap.add_argument("--fail-on-alarm", action="store_true", help="Exit 1 if any drift alarm fires")
    args = ap.parse_args()

    if not args.gen_hpp and not args.c3b_bin:
        ap.error("pass either --gen-hpp or --c3b-bin")

    bench_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.abspath(os.path.join(bench_dir, "..", ".."))

    with tempfile.TemporaryDirectory(prefix="kissat-telem-") as tmp_dir:
        c3b_runner = (
            compile_c3b_runner(args.gen_hpp, tmp_dir, repo_root, ext_telem=args.extended_telemetry)
            if args.gen_hpp else None
        )
        cases = load_benchmarks(args, tmp_dir, bench_dir)
        results = []
        total_alarms = 0

        for c in cases:
            wb = max(args.work_bytes, c["work_bytes"])
            c1 = run_c1(args.kissat, c["path"], args.timeout)
            c3b = (
                run_c3b_runner(c3b_runner, c["path"], wb, args.fuel, args.timeout)
                if c3b_runner else
                run_c3b_cli(args.c3b_bin, c["path"], wb, args.fuel, args.timeout,
                            ext_telem=args.extended_telemetry)
            )
            wm, alarms = detect_alarms(c1, c3b, args.inproc_min_c1, args.ticks_min_confl)
            total_alarms += len(alarms)
            results.append({
                "name": c["name"], "c1": c1, "c3b": c3b, "watermarks": wm, "alarms": alarms,
            })
            al_str = ";".join(alarms) if alarms else "OK"
            print(f"{c['name']:<34} C1={c1['status']} C3b={c3b['status']} {al_str}", flush=True)

        agg = {}
        for m in TELEM_METRICS:
            vals = [(r["c1"].get(m), r["c3b"].get(m)) for r in results]
            both = [(a, b) for a, b in vals if a is not None and b is not None]
            s1, s3 = sum(a for a, _ in both), sum(b for _, b in both)
            if not both:
                ratio = "n/a"
            elif s1 > 0:
                ratio = f"{s3 / s1:.3f}x"
            else:
                ratio = "1.000x" if s3 == 0 else "inf"
            agg[m] = {"cases": len(both), "sum_c1": s1, "sum_c3b": s3, "ratio": ratio}

        md = build_markdown(results, agg)
        if args.md_out:
            os.makedirs(os.path.dirname(os.path.abspath(args.md_out)), exist_ok=True)
            with open(args.md_out, "w", encoding="utf-8") as f:
                f.write(md)
        if args.json_out:
            os.makedirs(os.path.dirname(os.path.abspath(args.json_out)), exist_ok=True)
            with open(args.json_out, "w", encoding="utf-8") as f:
                json.dump(
                    {"cases": results, "aggregate": agg, "total_alarms": total_alarms},
                    f, indent=2,
                )

        print(f"Summary: cases={len(results)} total_alarms={total_alarms}")
        if args.fail_on_alarm and total_alarms > 0:
            sys.exit(1)


if __name__ == "__main__":
    main()
