#!/usr/bin/env python3

import argparse
import concurrent.futures
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

PROJECT_DIR = Path(__file__).resolve().parents[3]
BIN = PROJECT_DIR / ".lake/build/bin/bedrock2c"
BASE_FLAGS = ["-std=c11", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function",
              "-fstrict-aliasing", "-fno-sanitize-recover=all", "-ftrivial-auto-var-init=pattern"]
SANITIZERS = "undefined,address"
COMPILERS = ["gcc", "clang"]
ARCHS = ["-m64", "-m32"]
OPTS = [["-O0"], ["-O3", "-flto"]]
ENV = dict(os.environ, ASAN_OPTIONS="detect_leaks=0", UBSAN_OPTIONS="print_stacktrace=1")
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


def probe_sanitizers(cc, arch, tmp):
    src = tmp / "probe.c"
    src.write_text(PROBE)
    for san in [SANITIZERS, "undefined"]:
        exe = tmp / f"probe-{cc}{arch}-{san.replace(',', '_')}"
        try:
            r = run([cc, arch, *BASE_FLAGS, f"-fsanitize={san}", str(src), "-o", str(exe)], 120)
            if r.returncode == 0 and run([str(exe)], 30).stdout == "ok\n":
                return san
        except (OSError, subprocess.TimeoutExpired):
            pass
    return None


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
        return "MISMATCH", detail
    return "PASS", ""


def run_one(exe_cmd, case, src, cfg, tmp):
    tag = f"{case}-{cfg['name']}"
    exe = tmp / tag
    flags = [cfg["arch"], *BASE_FLAGS, *cfg["opt"]]
    if cfg["san"]:
        flags.append(f"-fsanitize={cfg['san']}")
    try:
        r = run([cfg["cc"], *flags, str(src), "-o", str(exe)], 300)
        if r.returncode != 0:
            return "FAIL", f"compile: {r.stderr.strip()[:2000]}"
        r = run([str(exe)], 60)
        if r.returncode != 0:
            return "FAIL", f"run exited {r.returncode}: {r.stderr.strip()[:2000]}"
        c_out = json.loads(r.stdout)
        r = run([*exe_cmd, "replay", case], 300, input=r.stdout)
        if r.returncode != 0:
            return "FAIL", f"replay exited {r.returncode}: {r.stderr.strip()[:2000]}"
        return compare(case, cfg, c_out, json.loads(r.stdout))
    except subprocess.TimeoutExpired as e:
        return "FAIL", f"timeout: {e.cmd}"
    except (OSError, json.JSONDecodeError) as e:
        return "FAIL", str(e)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("cases", nargs="*")
    ap.add_argument("--bedrock2c")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 1)
    ap.add_argument("--keep", action="store_true")
    args = ap.parse_args()

    exe_cmd = bedrock2c_cmd(args.bedrock2c)
    if exe_cmd is None:
        return 1
    r = run([*exe_cmd, "list"], 1800)
    if r.returncode != 0:
        print(f"bedrock2c list failed: {r.stderr}")
        return 1
    all_cases = r.stdout.split()
    cases = args.cases or all_cases
    unknown = [c for c in cases if c not in all_cases]
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
            san = probe_sanitizers(cc, arch, tmp)
            if san is None:
                results.append(("*", f"{cc}{arch}", "FAIL", "cannot build a sanitized program"))
                continue
            if san != SANITIZERS:
                notes.append(f"{cc} {arch}: AddressSanitizer unavailable, using -fsanitize={san}")
            for opt in OPTS:
                configs.append({"cc": cc, "arch": arch, "opt": opt, "san": san,
                                "name": f"{cc}{arch}{''.join(opt)}"})

    srcs = {}
    for case in cases:
        src = tmp / f"{case}.c"
        try:
            r = run([*exe_cmd, "emit", case, "--out", str(src)], 300)
        except subprocess.TimeoutExpired:
            r = None
        if r is None or r.returncode != 0:
            results.append((case, "emit", "FAIL", r.stderr.strip() if r else "timeout"))
        else:
            srcs[case] = src

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = {pool.submit(run_one, exe_cmd, case, src, cfg, tmp): (case, cfg["name"])
                for case, src in srcs.items() for cfg in configs}
        for fut in concurrent.futures.as_completed(futs):
            case, name = futs[fut]
            results.append((case, name, *fut.result()))

    results.sort(key=lambda x: (x[0], x[1]))
    for case, name, status, detail in results:
        if status != "PASS":
            print(f"{status:8} {case} [{name}] {detail}")
    for note in notes:
        print(f"NOTE: {note}")
    counts = {}
    for _, _, status, _ in results:
        counts[status] = counts.get(status, 0) + 1
    print(f"{len(srcs)} cases x {len(configs)} configs: " +
          ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    for cfg in configs:
        n = sum(1 for _, name, s, _ in results if name == cfg["name"] and s == "PASS")
        print(f"  {cfg['name']:24} -fsanitize={cfg['san']:18} {n}/{len(srcs)} passed")
    if args.keep:
        print(f"artifacts kept in {tmp}")
    else:
        shutil.rmtree(tmp, ignore_errors=True)
    return 0 if results and all(s == "PASS" for _, _, s, _ in results) else 1


if __name__ == "__main__":
    sys.exit(main())
