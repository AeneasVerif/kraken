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
import subprocess
import sys
import tempfile

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


def evaluate_canary(entry, rec, baseline_rec=None, strict_gaps=False):
    issues = []
    gaps = []
    fname = entry["file"]
    st = rec.get("status", -1)
    if st == 10:
        issues.append(f"SOUNDNESS BUG: got SAT (10) on UNSAT canary {fname}!")
    elif st != 20:
        msg = f"unsolved (status={st}, timeout={rec.get('timeout')}, oom={rec.get('oom', 0)})"
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

        if "k_conflicts" in rec and rec.get("k_status") == 20:
            kc = rec["k_conflicts"]
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


def main():
    ap = argparse.ArgumentParser(description="Run and verify 10-family Kissat UNSAT canaries.")
    ap.add_argument("--cnf-dir", help="Directory with generated canaries (auto-generated if omitted)")
    ap.add_argument("--full-c4", help="Path to C4 native x64 Full bench_main binary")
    ap.add_argument("--full-c3b", help="Path to C3b PrintCpp-native-mem Full bench_main binary")
    ap.add_argument("--fast-c4", help="Path to C4 native x64 FullFast bench_main binary")
    ap.add_argument("--fast-c3b", help="Path to C3b PrintCpp-native-mem FullFast bench_main binary")
    ap.add_argument("--m3-c4", help="Path to C4 native x64 FullM3 bench_main binary")
    ap.add_argument("--m3-c3b", help="Path to C3b PrintCpp-native-mem FullM3 bench_main binary")
    ap.add_argument("--kissat", help="Optional path to upstream Kissat 4.0.4 binary")
    ap.add_argument("--work-bytes", type=int, default=67108864, help="Workspace bytes (default 64 MiB)")
    ap.add_argument("--fuel", type=int, default=200000000, help="Solver fuel budget")
    ap.add_argument("--per-timeout", type=int, default=5, help="Per-CNF timeout in seconds (default 5)")
    ap.add_argument("--baseline", default="bench/kissat/canary_baseline.json", help="Baseline JSON path")
    ap.add_argument("--update-baseline", action="store_true", help="Write measured baseline JSON")
    ap.add_argument("--commit", default="", help="Git commit SHA to stamp into baseline JSON")
    ap.add_argument("--strict-gaps", action="store_true", help="Treat known pre-M3 gaps as hard failures")
    ap.add_argument("--filter", default="", help="Substring filter on canary filename")
    args = ap.parse_args()

    if not any([args.full_c4, args.full_c3b, args.fast_c4, args.fast_c3b, args.m3_c4, args.m3_c3b]):
        ap.error(
            "specify at least one solver binary "
            "(--full-c4/--full-c3b/--fast-c4/--fast-c3b/--m3-c4/--m3-c3b)"
        )

    tmp_ctx = None
    cnf_dir = args.cnf_dir
    if not cnf_dir:
        tmp_ctx = tempfile.TemporaryDirectory(prefix="kissat-canaries-")
        cnf_dir = tmp_ctx.name
        gen_script = os.path.join(os.path.dirname(os.path.abspath(__file__)), "gen_canary_cnfs.py")
        subprocess.run(["timeout", "60", sys.executable, "-B", gen_script, cnf_dir], check=True)

    with open(os.path.join(cnf_dir, "manifest.json"), encoding="utf-8") as f:
        manifest = json.load(f)["canaries"]
    if args.filter:
        manifest = [e for e in manifest if args.filter in e["file"]]

    baseline = None
    if not args.update_baseline and os.path.exists(args.baseline):
        with open(args.baseline, encoding="utf-8") as f:
            baseline = json.load(f)

    configs = []
    if args.full_c4:
        configs.append(("Full_C4", args.full_c4, False, args.kissat))
    if args.full_c3b:
        configs.append(("Full_C3b", args.full_c3b, False, None))
    if args.fast_c4:
        configs.append(("FullFast_C4", args.fast_c4, True, args.kissat if not args.full_c4 else None))
    if args.fast_c3b:
        configs.append(("FullFast_C3b", args.fast_c3b, True, None))
    if args.m3_c4:
        k_m3 = args.kissat if not (args.full_c4 or args.fast_c4) else None
        configs.append(("FullM3_C4", args.m3_c4, True, k_m3))
    if args.m3_c3b:
        configs.append(("FullM3_C3b", args.m3_c3b, True, None))

    results = {}
    hard_fails = []
    parity_fails = []
    all_gaps = []

    hdr = (
        f"{'Canary':<28} {'Cfg':<12} {'St':>3} {'ms':>8} {'Confl':>8} "
        f"{'Ticks':>10} {'BVA':>4} {'Cong':>4} {'Swp':>4} {'Viv':>4} {'BVE':>4} {'Trns':>5} {'Red':>4}"
    )
    print(hdr)
    print("-" * len(hdr))

    for entry in manifest:
        fname = entry["file"]
        cpath = os.path.join(cnf_dir, fname)
        row = {"family": entry["family"], "expected_gap": entry.get("expected_gap", ""), "runs": {}}
        for name, bpath, is_m2, kbin in configs:
            rec = run_one(bpath, cpath, args.work_bytes, args.fuel, args.per_timeout, is_m2, kbin)
            row["runs"][name] = compact_metrics(rec)
            st_s = "TO" if rec.get("timeout") else str(rec["status"])
            print(
                f"{fname:<28} {name:<12} {st_s:>3} {rec['ms']:>8.2f} "
                f"{rec.get('conflicts', 0):>8} {rec.get('search_ticks', 0):>10} "
                f"{rec.get('bva', 0):>4} {rec.get('cong', 0):>4} {rec.get('sweep', 0):>4} "
                f"{rec.get('viv', 0):>4} {rec.get('bve', 0):>4} {rec.get('trans', 0):>5} "
                f"{rec.get('reductions', 0):>4}"
            )
            base_rec = None
            if baseline and fname in baseline.get("canaries", {}):
                base_rec = baseline["canaries"][fname].get("runs", {}).get(name)
            issues, gaps = evaluate_canary(entry, rec, base_rec, args.strict_gaps)
            for msg in issues:
                hard_fails.append(f"{fname} [{name}]: {msg}")
            for msg in gaps:
                all_gaps.append(f"{fname} [{name}]: {msg}")

        # Bit-identical work parity check: C4 == C3b
        for base_mod in ("Full", "FullFast", "FullM3"):
            c4_k, c3b_k = f"{base_mod}_C4", f"{base_mod}_C3b"
            if c4_k in row["runs"] and c3b_k in row["runs"]:
                diffs = check_parity(base_mod, row["runs"][c4_k], row["runs"][c3b_k])
                if diffs:
                    parity_fails.append(f"{fname} [{base_mod} C4 vs C3b]: " + "; ".join(diffs))

        results[fname] = row

    print("\n== Canary Summary ==")
    for name, _, _, _ in configs:
        solved = sum(1 for r in results.values() if r["runs"][name].get("status") == 20)
        tot = len(results)
        tot_ms = sum(r["runs"][name]["ms"] for r in results.values())
        print(f"  {name:<14}: {solved:2d}/{tot} UNSAT solved  (total {tot_ms:.1f} ms)")

    for base_mod in ("Full", "FullFast", "FullM3"):
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
