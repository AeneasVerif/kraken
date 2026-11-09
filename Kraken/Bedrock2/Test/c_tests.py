#!/usr/bin/env python3

import argparse
import concurrent.futures
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

PROJECT_DIR = Path(__file__).resolve().parents[3]
BIN = PROJECT_DIR / ".lake/build/bin/bedrock2c"
BASE_FLAGS = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function",
              "-Wno-tautological-compare", "-Wno-type-limits", "-fstrict-aliasing",
              "-fno-sanitize-recover=all", "-ftrivial-auto-var-init=pattern", "-U_FORTIFY_SOURCE"]
CC_FLAGS = {
    "gcc": ["-Wno-bool-compare", "-Wno-bool-operation", "-Wno-int-in-bool-context"],
    "clang": ["-Wno-bool-operation", "-Wno-int-in-bool-context"],
}
SANITIZER_SETS = ["undefined,address", "undefined"]
COMPILERS = ["gcc", "clang"]
ARCHS = ["-m64", "-m32"]
OPTS = [["-O0"], ["-O3", "-flto"]]
ENV = dict(os.environ, ASAN_OPTIONS="detect_leaks=0", UBSAN_OPTIONS="print_stacktrace=1")
XFAIL = [
    ("same_slot", "clang", lambda cfg: cfg["opt"][0] in ("-O2", "-O3") and "address" not in cfg["san"],
     "https://github.com/llvm/llvm-project/issues/45725"),
    ("bitcopy_store", "gcc", lambda cfg: cfg["opt"][0] in ("-O2", "-O3"),
     "https://gcc.gnu.org/bugzilla/show_bug.cgi?id=65752"),
]
XFAIL_C_RETS = {"same_slot": [1], "bitcopy_store": [0]}
OK_STATUSES = ("PASS", "XFAIL", "XPASS")
PROBE = "#include <stdio.h>\nint main(void) { printf(\"ok\\n\"); return 0; }\n"


def bedrock2c_cmd(override):
    if override:
        return [override]
    try:
        r = run(["lake", "build", "bedrock2c"], 3600)
    except subprocess.TimeoutExpired:
        print("lake build bedrock2c timed out")
        return None
    if r.returncode != 0:
        print(f"lake build bedrock2c failed:\n{r.stdout}{r.stderr}")
        return None
    return [str(BIN)]


def run(cmd, timeout, **kw):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, cwd=PROJECT_DIR,
                          env=ENV, **kw)


def probe_sanitizer(cc, arch, san, tmp):
    src = tmp / "probe.c"
    src.write_text(PROBE)
    exe = tmp / f"probe-{cc}{arch}-{san.replace(',', '_')}"
    try:
        r = run([cc, arch, *BASE_FLAGS, *CC_FLAGS.get(cc, []), f"-fsanitize={san}", str(src), "-o", str(exe)],
                120)
        return r.returncode == 0 and run([str(exe)], 30).stdout == "ok\n"
    except (OSError, subprocess.TimeoutExpired):
        return False


def apply_xfail(case, cfg, status, detail):
    for xcase, xcc, pred, ref in XFAIL:
        if xcase == case and xcc == cfg["cc"] and pred(cfg):
            if status == "MISMATCH":
                return "XFAIL", f"{ref} {detail}"
            if status == "PASS":
                return "XPASS", ref
    return status, detail


def compare(case, cfg, c_out, replay_out):
    want_ws = 4 if cfg["arch"] == "-m32" else 8
    if c_out.get("wordsize") != want_ws:
        return "FAIL", f"word size {c_out.get('wordsize')} != {want_ws}"
    status = replay_out.get("status")
    if status == "invalid":
        return "INVALID", json.dumps(replay_out)
    if status != "ok":
        return "FAIL", f"replay: {json.dumps(replay_out)}"
    diffs = [k for k in ("rets", "final") if c_out.get(k) != replay_out.get(k)]
    if diffs:
        detail = "; ".join(f"{k}: C={c_out.get(k)} Lean={replay_out.get(k)}" for k in diffs)
        if case in XFAIL_C_RETS and (diffs != ["rets"] or c_out.get("rets") != XFAIL_C_RETS[case]):
            return "FAIL", f"unexpected mismatch: {detail}"
        return "MISMATCH", detail
    return "PASS", ""


def run_one(exe_cmd, case, src, cfg, tmp):
    tag = f"{case}-{cfg['name']}"
    exe = tmp / tag
    flags = [cfg["arch"], *BASE_FLAGS, *CC_FLAGS.get(cfg["cc"], []), *cfg["opt"]]
    if cfg["san"]:
        flags.append(f"-fsanitize={cfg['san']}")
    art = {"flags.txt": " ".join([cfg["cc"], *flags]) + "\n"}
    try:
        r = run([cfg["cc"], *flags, str(src), "-o", str(exe)], 300)
        art["compile.txt"] = r.stderr
        if r.returncode != 0:
            return "FAIL", f"compile: {r.stderr.strip()[:2000]}", art
        r = run([str(exe)], 60)
        art["c_output.json"], art["c_stderr.txt"] = r.stdout, r.stderr
        if r.returncode != 0:
            return "FAIL", f"run exited {r.returncode}: {r.stderr.strip()[:2000]}", art
        c_out = json.loads(r.stdout)
        r = run([*exe_cmd, "replay", case], 300, input=r.stdout)
        art["replay.json"], art["replay_stderr.txt"] = r.stdout, r.stderr
        if r.returncode != 0:
            return "FAIL", f"replay exited {r.returncode}: {r.stderr.strip()[:2000]}", art
        return (*apply_xfail(case, cfg, *compare(case, cfg, c_out, json.loads(r.stdout))), art)
    except subprocess.TimeoutExpired as e:
        return "FAIL", f"timeout: {e.cmd}", art
    except (OSError, json.JSONDecodeError) as e:
        return "FAIL", str(e), art


def save_failure(exe_cmd, root, case, name, src, art):
    d = Path(root) / case
    (d / name).mkdir(parents=True, exist_ok=True)
    if src is not None and src.exists():
        shutil.copy(src, d / f"{case}.c")
    try:
        r = run([*exe_cmd, "show", case], 300)
        (d / "case.txt").write_text(r.stdout + r.stderr)
    except subprocess.TimeoutExpired:
        pass
    for fname, text in art.items():
        (d / name / fname).write_text(text or "")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cases", nargs="*")
    ap.add_argument("--bedrock2c")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--keep", action="store_true")
    ap.add_argument("--gen", nargs=2, type=int, metavar=("SEED", "COUNT"))
    ap.add_argument("--no-corpus", action="store_true")
    ap.add_argument("--config-filter", default="")
    ap.add_argument("--save-failures", metavar="DIR")
    args = ap.parse_args()

    exe_cmd = bedrock2c_cmd(args.bedrock2c)
    if exe_cmd is None:
        return 1
    r = run([*exe_cmd, "list"], 1800)
    if r.returncode != 0:
        print(f"bedrock2c list failed: {r.stderr}")
        return 1
    all_cases = r.stdout.split()
    cases = args.cases or ([] if args.no_corpus else all_cases)
    if args.gen:
        r = run([*exe_cmd, "gen", str(args.gen[0]), str(args.gen[1])], 1800)
        if r.returncode != 0:
            print(f"bedrock2c gen failed: {r.stderr}")
            return 1
        cases = cases + r.stdout.split()
    unknown = [c for c in cases if c not in all_cases and not c.startswith("gen_")]
    if unknown:
        print(f"unknown cases: {unknown}")
        return 1

    tmp = Path(tempfile.mkdtemp(prefix="bedrock2c-"))
    results = []
    configs = []
    notes = []
    for cc in COMPILERS:
        if not shutil.which(cc):
            results.append(("*", cc, "FAIL", f"compiler {cc} not found"))
            continue
        for arch in ARCHS:
            for san in SANITIZER_SETS:
                if not probe_sanitizer(cc, arch, san, tmp):
                    if "address" in san:
                        notes.append(f"{cc} {arch}: AddressSanitizer unavailable, skipping -fsanitize={san}")
                    else:
                        results.append(("*", f"{cc}{arch}", "FAIL", f"cannot build with -fsanitize={san}"))
                    continue
                tag = "asan" if "address" in san else "ubsan"
                for opt in OPTS:
                    name = f"{cc}{arch}{''.join(opt)}-{tag}"
                    if re.search(args.config_filter, name):
                        configs.append({"cc": cc, "arch": arch, "opt": opt, "san": san, "name": name})

    srcs = {}
    for case in cases:
        src = tmp / f"{case}.c"
        try:
            r = run([*exe_cmd, "emit", case, "--out", str(src)], 300)
        except subprocess.TimeoutExpired:
            r = None
        if r is None or r.returncode != 0:
            results.append((case, "emit", "FAIL", r.stderr.strip() if r else "timeout"))
            if args.save_failures:
                save_failure(exe_cmd, args.save_failures, case, "emit", None,
                             {"emit_stderr.txt": r.stderr if r else "timeout"})
        else:
            srcs[case] = src

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = {pool.submit(run_one, exe_cmd, case, src, cfg, tmp): (case, cfg["name"])
                for case, src in srcs.items() for cfg in configs}
        for fut in concurrent.futures.as_completed(futs):
            case, name = futs[fut]
            status, detail, art = fut.result()
            results.append((case, name, status, detail))
            if args.save_failures and status not in OK_STATUSES:
                save_failure(exe_cmd, args.save_failures, case, name, srcs[case], art)

    results.sort(key=lambda x: (x[0], x[1]))
    for case, name, status, detail in results:
        if status != "PASS":
            label = "WARNING XPASS" if status == "XPASS" else status
            print(f"{label:8} {case} [{name}] {detail}")
    for note in notes:
        print(f"NOTE: {note}")
    counts = {}
    for _, _, status, _ in results:
        counts[status] = counts.get(status, 0) + 1
    print(f"{len(srcs)} cases x {len(configs)} configs: " +
          ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    for cfg in configs:
        n = sum(1 for _, name, s, _ in results if name == cfg["name"] and s in OK_STATUSES)
        print(f"  {cfg['name']:30} -fsanitize={cfg['san']:18} {n}/{len(srcs)} ok")
    if args.save_failures and any(s not in OK_STATUSES for _, _, s, _ in results):
        print(f"failing programs saved to {args.save_failures}")
    if args.keep:
        print(f"artifacts kept in {tmp}")
    else:
        shutil.rmtree(tmp, ignore_errors=True)
    return 0 if results and all(s in OK_STATUSES for _, _, s, _ in results) else 1


if __name__ == "__main__":
    sys.exit(main())
