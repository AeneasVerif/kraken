#!/usr/bin/env python3
"""Reproducible 4-Way Stage-1 (140-CNF) Kissat Benchmark Harness.

Builds and evaluates all four performance-isolation corners on the Stage-1 suite
(`PV-35`, `Hard-24`, `SV-21`, `quick60`):

  - C1        : Upstream Kissat 4.0.4 (`clang -O3`)
  - C0-direct : Direct C0 -> C99 extraction (`clang -std=c99 -O3 -fwrapv -fno-strict-aliasing`)
  - C3b       : `LeanQbe.T` -> `PrintCpp` (`clang++ -std=c++20 -O3 -DTQBE_NATIVE_MEM`)
  - C4        : `LeanQbe.T` certified x86-64 machine code (`toATTAligned`, linked `-no-pie`)

All three C0-derived corners (`C0-direct`, `C3b`, `C4`) link against the exact same
`bench/kissat/bench_main.o` harness (with `PROT_NONE` guard pages and full DIMACS model
verification). The runner checks zero verdict disagreements across all 4 engines, 100% SAT
DIMACS model verification, and bit-exact 35-key telemetry parity (`C0-direct == C3b == C4`).
"""

import argparse
import concurrent.futures
import datetime
import json
import math
import os
import pathlib
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True

ROOT = pathlib.Path(__file__).resolve().parents[2]

DEFAULT_MANIFEST_CANDIDATES = tuple(
    p for p in (
        pathlib.Path(os.environ["STAGE1_MANIFEST"]) if "STAGE1_MANIFEST" in os.environ else None,
        ROOT / "bench/kissat/manifest_stage1.json",
    ) if p is not None
)

DEFAULT_C1_CANDIDATES = tuple(
    p for p in (
        pathlib.Path(os.environ["KISSAT_REF_BIN"]) if "KISSAT_REF_BIN" in os.environ else None,
        pathlib.Path(os.environ["KISSAT_BIN"]) if "KISSAT_BIN" in os.environ else None,
        ROOT / "scratch/kissat-ref-clang/build/kissat",
        ROOT / "scratch/kissat/build/kissat",
    ) if p is not None
)

SUITE_ORDER = (
    ("pv35", "PV-35"),
    ("hard24", "Hard-24"),
    ("sv21", "SV-21"),
    ("quick60", "quick60"),
)

ALL_TELEM_KEYS = (
    "status", "conflicts", "learned_lits", "min_removed", "num_irred",
    "num_redundant", "num_binary", "switched", "search_ticks", "rephased",
    "reductions", "tier1", "tier2", "restarts", "oom", "max_vars", "cur_vars",
    "unassigned", "otfs", "eager_sub", "probings", "eliminations", "elim_bound",
    "hbr", "trans", "viv", "subst", "cong", "sweep", "bve", "bce", "bva",
    "walks", "last_probe_ticks", "last_elim_ticks",
)


def load_solvers_registry():
    solvers_file = ROOT / "bench/kissat/solvers.json"
    with open(solvers_file, "r", encoding="utf-8") as f:
        return json.load(f)


def default_module():
    if (ROOT / "LeanQbe/T/Examples/Kissat/Src/Full.lean").is_file() or (
        ROOT / "LeanQbe/T/Examples/Kissat/FullFidelityAssemblyStep12.lean"
    ).is_file():
        return "KissatFidelity"
    return "Plain"


def resolve_module_spec(raw_name):
    key = raw_name.strip().lower()
    registry = load_solvers_registry()
    matched = None
    for mod_name, entry in registry.items():
        if key == mod_name.lower() or key in [a.lower() for a in entry.get("aliases", [])]:
            matched = entry
            break
    if not matched:
        raise SystemExit(
            f"ERROR: unknown --module '{raw_name}' "
            "(expected KissatFidelity|KissatM8Opt|Plain)"
        )
    mod = matched["module"]
    kdir = ROOT / "LeanQbe/T/Examples/Kissat"
    lean_file = matched["mod_file"]
    if not (kdir / f"{lean_file}.lean").is_file():
        raise SystemExit(f"ERROR: {kdir / f'{lean_file}.lean'} is not present in {ROOT}")

    extra_imports = list(matched.get("extra_imports", []))
    fns_expr = matched["fns_expr"]
    policy_desc = matched["policy_desc"]
    cert_x64 = (ROOT / matched["cert_x64_file"]).is_file() if "cert_x64_file" in matched else False

    if mod == "KissatFidelity":
        if (kdir / "Src/InlPolicy.lean").is_file():
            extra_imports = ["LeanQbe.T.MainInline", "LeanQbe.T.Examples.Kissat.Src.InlPolicy"]
            fns_expr = (
                f"(({matched['mod_expr']}).optInlinePolicy "
                "LeanQbe.T.Examples.Kissat.Src.InlPolicy.kissatInlPolicy).fns"
            )
            policy_desc = "kissatInlPolicy"
        else:
            extra_imports = []
            fns_expr = f"({matched['mod_expr']}).fns"
            policy_desc = "uninlined kissatModule.fns (Src.InlPolicy not present)"
    elif mod == "KissatM8Opt":
        if (kdir / "FullM8InlPolicy.lean").is_file():
            extra_imports = ["LeanQbe.T.MainInline", "LeanQbe.T.Examples.Kissat.FullM8InlPolicy"]
            fns_expr = (
                "((LeanQbe.T.Examples.Kissat.FullM8OptAssembly.m8OptModule).optInlinePolicy "
                "LeanQbe.T.Examples.Kissat.FullM8InlPolicy.m8InlPolicy).fns"
            )
            policy_desc = "m8InlPolicy"
        else:
            extra_imports = []
            fns_expr = f"({matched['mod_expr']}).fns"
            policy_desc = "uninlined m8OptModule.fns (FullM8OptInl / Policy not present)"

    return {
        "module": mod,
        "tag": matched["tag"],
        "c0_target": matched["c0_target"],
        "lean_mod": matched["lean_mod"],
        "mod_expr": matched["mod_expr"],
        "extra_imports": extra_imports,
        "fns_expr": fns_expr,
        "policy_desc": policy_desc,
        "certified_x64": cert_x64,
        "is_fidelity": bool(matched.get("is_fidelity", False)),
        "is_solver_extension": bool(matched.get("is_solver_extension", False)),
    }


def resolve_manifest(cli_path):
    if cli_path:
        p = pathlib.Path(cli_path)
        if not p.is_file():
            raise SystemExit(f"ERROR: manifest not found: {p}")
        return p
    env_p = os.environ.get("STAGE1_MANIFEST")
    if env_p:
        p = pathlib.Path(env_p)
        if not p.is_file():
            raise SystemExit(f"ERROR: STAGE1_MANIFEST not found: {p}")
        return p
    for cand in DEFAULT_MANIFEST_CANDIDATES:
        if cand.is_file():
            return cand
    raise SystemExit(
        "ERROR: Stage-1 manifest not found; pass --manifest <path> or set STAGE1_MANIFEST."
    )


def resolve_c1_bin(cli_path):
    for cand in (cli_path, os.environ.get("KISSAT_C1_BIN"), os.environ.get("KISSAT_BIN")):
        if cand:
            resolved = shutil.which(cand) or cand
            if os.path.isfile(resolved) and os.access(resolved, os.X_OK):
                return pathlib.Path(resolved).resolve()
            raise SystemExit(f"ERROR: C1 kissat binary not found or not executable: {cand}")
    for cand in DEFAULT_C1_CANDIDATES:
        if cand.is_file() and os.access(cand, os.X_OK):
            return cand.resolve()
    found = shutil.which("kissat")
    if found:
        return pathlib.Path(found).resolve()
    raise SystemExit(
        "ERROR: upstream Kissat C1 binary not found; pass --c1-bin <path> or set KISSAT_C1_BIN."
    )


def run_cmd(cmd, timeout_s, cwd=ROOT, env=None, capture=False):
    full = ["timeout", "-k", "5s", f"{timeout_s}s"] + [str(c) for c in cmd]
    res = subprocess.run(
        full,
        cwd=str(cwd),
        env=env,
        stdout=subprocess.PIPE if capture else None,
        stderr=subprocess.PIPE if capture else None,
        text=True,
    )
    if res.returncode != 0:
        detail = ""
        if capture:
            detail = f"\nstdout:\n{res.stdout}\nstderr:\n{res.stderr}"
        raise RuntimeError(f"Command failed (rc={res.returncode}): {' '.join(full)}{detail}")
    return res


def geomean(vals):
    valid = [v for v in vals if v > 0]
    if not valid:
        return float("nan")
    return math.exp(sum(math.log(v) for v in valid) / len(valid))


def percentile(vals, p):
    if not vals:
        return float("nan")
    s = sorted(vals)
    k = (len(s) - 1) * (p / 100.0)
    f = math.floor(k)
    c = math.ceil(k)
    if f == c:
        return s[int(k)]
    return s[int(f)] * (c - k) + s[int(c)] * (k - f)


def get_text_size(path):
    res = run_cmd(["size", "-A", str(path)], timeout_s=30, capture=True)
    for line in res.stdout.splitlines():
        parts = line.split()
        if len(parts) >= 2 and parts[0] == ".text":
            return int(parts[1])
    raise ValueError(f"No .text section found in {path}")


def get_non_nop_insns(path):
    res = run_cmd(["objdump", "-d", str(path)], timeout_s=60, capture=True)
    count = 0
    hex_chars = frozenset("0123456789abcdefABCDEF")
    for line in res.stdout.splitlines():
        s = line.strip()
        if ":" not in s:
            continue
        addr_part = s.split(":", 1)[0].strip()
        if addr_part and all(c in hex_chars for c in addr_part):
            if "nop" not in s and "data16" not in s:
                count += 1
    return count


def verify_dimacs_model(cnf_path, stdout_text):
    vals = {}
    for line in stdout_text.splitlines():
        s = line.strip()
        if s.startswith("v ") or s == "v":
            for tok in s[1:].split():
                try:
                    lit = int(tok)
                except ValueError:
                    continue
                if lit != 0:
                    vals[abs(lit)] = lit > 0
    if not vals:
        return False, "no model values in stdout"

    clause_idx = 0
    cur_clause = []
    in_header = True
    with open(cnf_path, "rb") as f:
        for raw in f:
            s = raw.decode("ascii", errors="replace").strip()
            if not s or s.startswith("c"):
                continue
            if in_header:
                if s.startswith("p ") and "cnf" in s.split()[:2]:
                    in_header = False
                continue
            if s.startswith("%"):
                break
            for tok_str in s.split():
                if tok_str == "%":
                    break
                try:
                    lit = int(tok_str)
                except ValueError:
                    continue
                if lit == 0:
                    if not any(
                        (v in vals) and (vals[v] == (l > 0))
                        for l in cur_clause
                        for v in (abs(l),)
                    ):
                        return False, f"clause {clause_idx} unsatisfied"
                    cur_clause = []
                    clause_idx += 1
                else:
                    cur_clause.append(lit)
    if cur_clause:
        if not any((abs(l) in vals) and (vals[abs(l)] == (l > 0)) for l in cur_clause):
            return False, "trailing clause unsatisfied"
    return True, f"model ok ({clause_idx} clauses verified)"


def build_corners(spec, build_dir, c1_bin, cc, cxx, skip_lake_build, reuse_bins):
    build_dir = pathlib.Path(build_dir)
    build_dir.mkdir(parents=True, exist_ok=True)
    tag = spec["tag"]

    bins = {
        "c1": str(c1_bin),
        "c0direct": str(build_dir / f"bench_c0direct_{tag}"),
        "c3b": str(build_dir / f"bench_c3b_{tag}"),
        "c4": str(build_dir / f"bench_c4_{tag}"),
    }
    objs = {
        "c0direct": build_dir / f"{tag}_direct.o",
        "c3b": build_dir / f"{tag}_c3b.o",
        "c4": build_dir / f"{tag}_c4.o",
    }
    asm_path = build_dir / f"{tag}_c4_x64.s"
    hpp_path = build_dir / f"{tag}_gen.hpp"
    c_path = build_dir / f"{tag}_direct.c"
    bridge_path = build_dir / f"{tag}_c3b_bridge.cpp"
    main_obj = build_dir / "bench_main.o"
    timing_path = build_dir / "emit_timing.json"

    emit_timing = {}
    if reuse_bins and all(os.path.isfile(p) and os.access(p, os.X_OK) for p in bins.values()):
        print(f"== Reusing existing 4-corner binaries in {build_dir} ==", flush=True)
        if timing_path.is_file():
            emit_timing = json.loads(timing_path.read_text())
    else:
        print(f"== [Build 1/4] Common harness bench_main.o ({cc} -std=c99 -O3) ==", flush=True)
        run_cmd(
            [
                cc, "-std=c99", "-O3", "-Wall", "-Wextra", "-Werror",
                f"-I{ROOT / 'test/kissat'}",
                "-c", str(ROOT / "bench/kissat/bench_main.c"),
                "-o", str(main_obj),
            ],
            timeout_s=120,
        )

        print(f"== [Build 2/4] C0-direct ({spec['module']} -> C99 -> {cc} -O3) ==", flush=True)
        t0 = time.perf_counter()
        run_cmd(
            [
                sys.executable, "-B", str(ROOT / "bench/kissat/extract_c0_direct.py"),
                "--target", spec["c0_target"], "--out", str(c_path),
            ],
            timeout_s=60,
        )
        emit_timing["c0_extract_ms"] = round((time.perf_counter() - t0) * 1000.0, 1)
        c0_flags = [
            cc, "-std=c99", "-O3", "-fwrapv", "-fno-strict-aliasing",
            "-Wall", "-Wextra", "-Werror",
        ]
        if spec["c0_target"] == "plain":
            c0_flags.append("-Wno-parentheses")
        run_cmd(
            c0_flags + [
                f"-I{ROOT / 'LeanQbe/T/Frontend/C0'}",
                "-c", str(c_path), "-o", str(objs["c0direct"]),
            ],
            timeout_s=180,
        )
        run_cmd([cc, str(objs["c0direct"]), str(main_obj), "-o", bins["c0direct"]], timeout_s=120)

        stage_lean_path = os.environ.get("STAGE_LEAN_PATH")
        lake_targets = [
            spec["lean_mod"],
            "LeanQbe.T.PrintCpp",
            "LeanQbe.T.Opt",
            "LeanQbe.T.Driver",
            "LeanQbe.T.Amd64.Targ",
            "LeanQbe.T.Amd64.PrintATTAlign",
        ] + spec["extra_imports"]

        if not skip_lake_build and not stage_lean_path:
            print(f"== [Build 3/4] lake build {' '.join(lake_targets)} ==", flush=True)
            run_cmd(["lake", "build", "--wfail"] + lake_targets, timeout_s=3600)
        else:
            print("== [Build 3/4] Skipping lake build (prebuilt environment) ==", flush=True)

        extra_imp_lines = "\n".join(f"import {m}" for m in spec["extra_imports"])
        emit_lean = build_dir / f"Emit_{tag}.lean"
        emit_lean.write_text(
            f"""import {spec['lean_mod']}
import LeanQbe.T.PrintCpp
import LeanQbe.T.Opt
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign
{extra_imp_lines}

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Amd64

/-- Parallel per-function compilation matching `Driver.compileFns` and `LinkedCert.code`
directive-for-directive. -/
def compileFnsPar (I : Isa) (lt : LegalTarget) (fs : List Fn) :
    Except String (List I.Directive) :=
  let tasks := fs.map fun f => Task.spawn fun () =>
    let ef := Driver.matFn f.earlyOpt
    let mf := Fn.midFromEarly lt ef
    let h := Spill.hints I mf
    match Rega.lowerFn I h mf.ext mf with
    | .ok c => .ok c
    | .error e => .error s!"{{f.name}}: {{e}}"
  let rec collect : List (Task (Except String (List I.Directive))) →
      Except String (List I.Directive)
    | [] => .ok []
    | t :: rest => do
      let c ← t.get
      let cs ← collect rest
      .ok (c ++ cs)
  collect tasks

def main (args : List String) : IO Unit := do
  let [hppOut, asmOut, timingOut] := args | throw (IO.userError "usage: <hpp> <asm> <timing.json>")
  let m := {spec['mod_expr']}
  let tCpp0 ← IO.monoMsNow
  let cpp ← match ppTModule m with
    | .ok s => pure s
    | .error e => throw (IO.userError s!"PrintCpp error: {{e}}")
  IO.FS.writeFile hppOut cpp
  let tCpp1 ← IO.monoMsNow
  let tAsm0 ← IO.monoMsNow
  let fns := {spec['fns_expr']}
  let dirs ← match compileFnsPar x64Target.toIsa x64LegalTarget fns with
    | .ok d => pure d
    | .error e => throw (IO.userError s!"compileFnsPar error: {{e}}")
  let asm := Driver.emitAsm (fun c => toATTAligned c ++ "\\n") fns dirs
  IO.FS.writeFile asmOut asm
  let tAsm1 ← IO.monoMsNow
  let cppMs := tCpp1 - tCpp0
  let asmMs := tAsm1 - tAsm0
  IO.println s!"[{spec['module']}] fns={{fns.length}} dirs={{dirs.length}} cpp={{cpp.length}}B ({{cppMs}}ms) asm={{asm.length}}B ({{asmMs}}ms)"
  let json := "{{\\"fn_count\\": " ++ toString fns.length ++
    ", \\"dir_count\\": " ++ toString dirs.length ++
    ", \\"cpp_emit_ms\\": " ++ toString cppMs ++
    ", \\"c4_emit_ms\\": " ++ toString asmMs ++ "}}"
  IO.FS.writeFile timingOut json
"""
        )

        print(f"== [Build 3b/4] Emit PrintCpp (.hpp) + C4 x86-64 (.s) for {spec['module']} ==", flush=True)
        if stage_lean_path:
            env = dict(os.environ)
            env["LEAN_PATH"] = stage_lean_path
            run_cmd(["lean", "--run", str(emit_lean), str(hpp_path), str(asm_path), str(timing_path)], timeout_s=600, env=env)
        else:
            run_cmd(["lake", "env", "lean", "--run", str(emit_lean), str(hpp_path), str(asm_path), str(timing_path)], timeout_s=600)
        emit_timing.update(json.loads(timing_path.read_text()))

        print(f"== [Build 4/4] Compile C3b ({cxx} -O3) + C4 ({cc} -no-pie) ==", flush=True)
        bridge_path.write_text(
            f"""#include <cstdint>
#include "tqbe_rt.hpp"

namespace tqbe_gen {{
#include "{hpp_path.name}"
}}

extern "C" uint64_t kissat_solve_bytes(
    const uint8_t *cnf_ptr, uint64_t cnf_len,
    uint8_t *work_ptr, uint64_t work_len, uint64_t fuel) {{
  ::tqbe::Mem mem;
  return tqbe_gen::kissat_solve_bytes(
      mem,
      ::tqbe::bits<64>(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(cnf_ptr))),
      ::tqbe::bits<64>(cnf_len),
      ::tqbe::bits<64>(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(work_ptr))),
      ::tqbe::bits<64>(work_len),
      ::tqbe::bits<64>(fuel)).word(0);
}}
"""
        )
        run_cmd(
            [
                cxx, "-std=c++20", "-O3", "-Wall", "-Wextra", "-Werror",
                "-DTQBE_NATIVE_MEM",
                f"-I{ROOT / 'LeanQbe/T/Runtime'}", f"-I{build_dir}",
                "-c", str(bridge_path), "-o", str(objs["c3b"]),
            ],
            timeout_s=300,
        )
        run_cmd([cxx, str(objs["c3b"]), str(main_obj), "-o", bins["c3b"]], timeout_s=120)

        run_cmd([cc, "-c", str(asm_path), "-o", str(objs["c4"])], timeout_s=120)
        run_cmd([cc, "-no-pie", str(objs["c4"]), str(main_obj), "-o", bins["c4"]], timeout_s=120)
        timing_path.write_text(json.dumps(emit_timing, indent=2))

    code_sizes = {}
    for k in ("c1", "c0direct", "c3b", "c4"):
        info = {"bin_text_bytes": get_text_size(bins[k])}
        if k in objs and objs[k].is_file():
            info["obj_text_bytes"] = get_text_size(objs[k])
            info["non_nop_insns"] = get_non_nop_insns(objs[k])
        else:
            info["obj_text_bytes"] = None
            info["non_nop_insns"] = get_non_nop_insns(bins[k])
        if k == "c4" and asm_path.is_file():
            info["asm_bytes"] = asm_path.stat().st_size
        code_sizes[k] = info

    return bins, code_sizes, emit_timing


def run_c1_trial(c1_bin, entry, cnf_path, timeout_s):
    cmd = ["timeout", "-k", "2s", f"{timeout_s:.1f}s", c1_bin, cnf_path]
    t0 = time.perf_counter()
    res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    out = res.stdout

    rc = res.returncode
    status = 0
    timed_out = False
    if rc in (124, 137):
        status = -1
        timed_out = True
    elif rc == 10 or "s SATISFIABLE" in out:
        status = 10
    elif rc == 20 or "s UNSATISFIABLE" in out:
        status = 20

    m_proc = re.search(r"c\s+process-time:\s+([0-9.]+)\s+seconds", out)
    internal_ms = float(m_proc.group(1)) * 1000.0 if m_proc else wall_ms
    m_conf = re.search(r"c\s+conflicts:\s+(\d+)", out)
    conflicts = int(m_conf.group(1)) if m_conf else -1

    model_ok = True
    model_msg = "n/a"
    if status == 10:
        model_ok, model_msg = verify_dimacs_model(cnf_path, out)
    elif status not in (10, 20, -1):
        model_ok = False
        model_msg = f"unknown status {status}"

    exp = entry.get("expected_verdict")
    verdict_ok = not ((status == 10 and exp == "unsat") or (status == 20 and exp == "sat"))

    return {
        "status": status,
        "wall_ms": min(wall_ms, timeout_s * 1000.0) if timed_out else wall_ms,
        "internal_ms": timeout_s * 1000.0 if timed_out else internal_ms,
        "conflicts": conflicts,
        "model_ok": model_ok,
        "model_msg": model_msg,
        "verdict_ok": verdict_ok,
        "timed_out": timed_out,
        "oom": 0,
        "raw_rc": rc,
    }


def run_c0_trial(bin_path, entry, cnf_path, timeout_s, work_mb_override, fuel):
    work_mb = work_mb_override if work_mb_override is not None else entry.get("min_work_mb", 64)
    work_bytes = int(work_mb) * 1024 * 1024
    cmd = [
        "timeout", "-k", "2s", f"{timeout_s:.1f}s",
        bin_path, "--full-telemetry-m2", str(work_bytes), str(fuel), cnf_path,
    ]
    t0 = time.perf_counter()
    res = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    wall_ms = (time.perf_counter() - t0) * 1000.0
    out = res.stdout

    if res.returncode in (124, 137):
        return {
            "status": -1,
            "wall_ms": min(wall_ms, timeout_s * 1000.0),
            "internal_ms": timeout_s * 1000.0,
            "conflicts": -1,
            "oom": 0,
            "timed_out": True,
            "model_ok": True,
            "model_msg": "timeout",
            "verdict_ok": True,
            "raw_rc": res.returncode,
        }

    parsed = None
    for line in out.splitlines():
        if "\t" in line and not line.startswith("FullHdr") and not line.startswith("c "):
            parts = line.strip().split("\t")
            if len(parts) >= 3:
                try:
                    st = int(parts[1])
                    ims = float(parts[2])
                except ValueError:
                    continue
                kv = {}
                for tok in parts[3:]:
                    if "=" in tok:
                        k, v = tok.split("=", 1)
                        try:
                            kv[k] = int(v)
                        except ValueError:
                            kv[k] = v
                parsed = (st, ims, kv)
                break

    if parsed is None or res.returncode != 0:
        return {
            "status": -2,
            "wall_ms": wall_ms,
            "internal_ms": wall_ms,
            "conflicts": -1,
            "oom": 0,
            "timed_out": False,
            "model_ok": False,
            "model_msg": f"exit_{res.returncode}",
            "verdict_ok": False,
            "raw_rc": res.returncode,
            "error": f"exit_{res.returncode}:{out.strip()[-120:]}",
        }

    st, ims, kv = parsed
    exp = entry.get("expected_verdict")
    verdict_ok = not ((st == 10 and exp == "unsat") or (st == 20 and exp == "sat"))
    oom = kv.get("oom", 0)
    # bench_main.c runs kissat_verify_dimacs_model on status==10 and exits non-zero on failure.
    model_ok = (st in (10, 20, 0)) and (oom == 0 if st in (10, 20) else True)
    model_msg = "verified_in_harness" if st == 10 and model_ok else ("unsat" if st == 20 else "ok")

    ret = {
        "status": st,
        "wall_ms": wall_ms,
        "internal_ms": ims,
        "timed_out": False,
        "model_ok": model_ok,
        "model_msg": model_msg,
        "verdict_ok": verdict_ok,
        "raw_rc": res.returncode,
    }
    ret.update(kv)
    return ret


def compute_solver_stats(rows, skey, timeout_s):
    solved = sat = unsat = to_cnt = oom_cnt = st0_cnt = sound_err = 0
    for r in rows:
        d = r[skey]
        st = d["status"]
        if not d.get("model_ok", True) or not d.get("verdict_ok", True):
            sound_err += 1
        if not d.get("timed_out") and st in (10, 20):
            solved += 1
            if st == 10:
                sat += 1
            else:
                unsat += 1
        elif st == -1 or d.get("timed_out"):
            to_cnt += 1
        elif d.get("oom", 0):
            oom_cnt += 1
        else:
            st0_cnt += 1
    return {
        "n": len(rows),
        "solved": solved,
        "sat": sat,
        "unsat": unsat,
        "timeout": to_cnt,
        "oom": oom_cnt,
        "st0": st0_cnt,
        "sound_err": sound_err,
    }


def compute_pair_ratios(rows, sa, sb, floor_ms):
    common_idx = [
        i for i, r in enumerate(rows)
        if (not r[sa].get("timed_out") and r[sa]["status"] in (10, 20))
        and (not r[sb].get("timed_out") and r[sb]["status"] in (10, 20))
    ]
    n_both = len(common_idx)
    if n_both == 0:
        return {
            "both_solved": 0,
            "wall_gm": float("nan"), "wall_med": float("nan"), "wall_p90": float("nan"),
            "wall_am_ratio": float("nan"),
            "int_gm": float("nan"), "int_med": float("nan"), "int_p90": float("nan"),
            "int_am_ratio": float("nan"),
        }
    wall_ratios, int_ratios = [], []
    sum_wa = sum_wb = sum_ia = sum_ib = 0.0
    for i in common_idx:
        ra, rb = rows[i][sa], rows[i][sb]
        wall_ratios.append(max(floor_ms, ra["wall_ms"]) / max(floor_ms, rb["wall_ms"]))
        int_ratios.append(max(floor_ms, ra["internal_ms"]) / max(floor_ms, rb["internal_ms"]))
        sum_wa += ra["wall_ms"]
        sum_wb += rb["wall_ms"]
        sum_ia += ra["internal_ms"]
        sum_ib += rb["internal_ms"]
    return {
        "both_solved": n_both,
        "wall_gm": geomean(wall_ratios),
        "wall_med": statistics.median(wall_ratios),
        "wall_p90": percentile(wall_ratios, 90.0),
        "wall_am_ratio": (sum_wa / sum_wb) if sum_wb > 0 else float("nan"),
        "int_gm": geomean(int_ratios),
        "int_med": statistics.median(int_ratios),
        "int_p90": percentile(int_ratios, 90.0),
        "int_am_ratio": (sum_ia / sum_ib) if sum_ib > 0 else float("nan"),
    }


def summarize_subset(rows, solvers, pairs, timeout_s, floor_ms):
    n = len(rows)
    solver_stats = {s: compute_solver_stats(rows, s, timeout_s) for s in solvers}
    penalty_s = 2.0 * timeout_s
    penalty_ms = penalty_s * 1000.0

    par2_all = {}
    for s in solvers:
        p2_am_vals = []
        p2_gm_vals = []
        all_wall = []
        for r in rows:
            d = r[s]
            all_wall.append(max(floor_ms, float(d["wall_ms"])))
            if not d.get("timed_out") and d["status"] in (10, 20):
                p2_am_vals.append(float(d["wall_ms"]) / 1000.0)
                p2_gm_vals.append(max(floor_ms, float(d["wall_ms"])))
            else:
                p2_am_vals.append(penalty_s)
                p2_gm_vals.append(penalty_ms)
        par2_all[s] = {
            "par2_am_s": (sum(p2_am_vals) / n) if n else float("nan"),
            "par2_gm_ms": geomean(p2_gm_vals),
            "all_wall_gm_ms": geomean(all_wall),
        }

    common_idx = [
        i for i, r in enumerate(rows)
        if all((not r[s].get("timed_out")) and r[s]["status"] in (10, 20) for s in solvers)
    ]
    n_com = len(common_idx)
    common = {}
    for s in solvers:
        if n_com > 0:
            w_am = sum(rows[i][s]["wall_ms"] for i in common_idx) / n_com
            i_am = sum(rows[i][s]["internal_ms"] for i in common_idx) / n_com
            w_gm = geomean([max(floor_ms, rows[i][s]["wall_ms"]) for i in common_idx])
            i_gm = geomean([max(floor_ms, rows[i][s]["internal_ms"]) for i in common_idx])
            common[s] = {
                "wall_am_ms": w_am,
                "wall_gm_ms": w_gm,
                "int_am_ms": i_am,
                "int_gm_ms": i_gm,
                "wall_minus_int_am_ms": w_am - i_am,
            }
        else:
            common[s] = {
                "wall_am_ms": float("nan"), "wall_gm_ms": float("nan"),
                "int_am_ms": float("nan"), "int_gm_ms": float("nan"),
                "wall_minus_int_am_ms": float("nan"),
            }

    ratios = {f"{a}_vs_{b}": compute_pair_ratios(rows, a, b, floor_ms) for a, b in pairs}
    par2_ratios = {}
    for a, b in pairs:
        ba = par2_all[a]
        bb = par2_all[b]
        par2_ratios[f"{a}_vs_{b}"] = {
            "par2_am_ratio": (ba["par2_am_s"] / bb["par2_am_s"]) if bb["par2_am_s"] > 0 else float("nan"),
            "par2_gm_ratio": (ba["par2_gm_ms"] / bb["par2_gm_ms"]) if bb["par2_gm_ms"] > 0 else float("nan"),
        }

    return {
        "n": n,
        "common_n": n_com,
        "solvers": solver_stats,
        "par2_all": par2_all,
        "common": common,
        "ratios": ratios,
        "par2_ratios": par2_ratios,
    }


def fmt_num(val, digits=1):
    return "—" if math.isnan(val) else f"{val:.{digits}f}"


def fmt_ratio_cell(rdict, key, bold=False):
    if key not in rdict:
        return "—"
    rv = rdict[key]
    if math.isnan(rv["wall_gm"]):
        return "—"
    s = (
        f"`{rv['wall_gm']:.4f}x / {rv['wall_am_ratio']:.4f}x`, "
        f"`{rv['int_gm']:.4f}x / {rv['int_am_ratio']:.4f}x`"
    )
    return f"**{s}**" if bold else s


def format_markdown(payload):
    meta = payload["meta"]
    ov = payload["overall"]
    ps = payload["per_suite"]
    par = payload["parity"]
    snd = payload["soundness"]
    sizes = payload["code_sizes"]
    mod = meta["module"]
    c4_label = f"C4 ({mod})"
    banner = "[NON-FIDELITY SOLVER EXTENSION] " if meta.get("ext_warning") else ""

    lines = [
        f"# {banner}Reproducible 4-Way Stage-1 Benchmark: `{mod}`",
        "",
        f"- **Date (UTC):** {meta['timestamp_utc']}",
        f"- **Benchmark Type:** `{meta.get('benchmark_type', 'compiler_evaluation')}` (`is_fidelity={meta.get('is_fidelity')}`, `is_solver_extension={meta.get('is_solver_extension')}`)",
        f"- **Git commit:** `{meta['git_rev']}`",
        f"- **Module / Policy:** `{mod}` (`{meta['fn_count']}` fns, `{meta['policy_desc']}`)",
        f"- **Compilers:** `{meta['cc_version']}` / `{meta['cxx_version']}`",
        f"- **Host / Load at start:** `{meta['cpu_model']}` (`{meta['nproc']}` vCPUs), loadavg `{meta['start_loadavg']}`",
        f"- **Parameters:** `{ov['n']}` CNFs, timeout `{meta['timeout_s']:.1f}s` (PAR-2 penalty `{2 * meta['timeout_s']:.1f}s`), floor `{meta['floor_ms']:.1f}ms`, `--jobs {meta['jobs']}`, fuel `{meta['fuel']:,}`, interleaved per-CNF engine order.",
        f"- **Verification:** `{snd['sound_errs']}` soundness/model errors, `{len(snd['disagreements'])}` cross-solver disagreements, `{par['total'] - par['diffs_count']}/{par['total']}` bit-exact 35-key C0 telemetry parity (`{par['diffs_count']}` diffs).",
        "",
        "## 4-Way Performance Matrix (`C1` vs `C0-direct` vs `C3b` vs `C4`)",
        "",
        f"*(Wall/Int AM and GM columns are evaluated on each row's strict 4-way common-solved subset; PAR-2 AM/GM cover all `N` instances with a `{2 * meta['timeout_s']:.1f}s` penalty; pairwise ratios use each pair's mutually solved subset with a `{meta['floor_ms']:.1f}ms` floor.)*",
        "",
        "| Suite (`N`, 4-way common) | Engine | Solved (`S/U`) | TO | Wall AM (ms) | Wall GM (ms) | Int AM (ms) | Int GM (ms) | `W - I` (ms) | PAR-2 AM (s) | PAR-2 GM (ms) | `vs C0-direct` (W-GM/AM, I-GM/AM) | `vs C3b` (W-GM/AM, I-GM/AM) | `vs C1` (W-GM/AM, I-GM/AM) |",
        "|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---|---|",
    ]

    def append_block(label, sub):
        first = True
        for skey, sdisp in (
            ("c1", "`C1`"),
            ("c0direct", "**`C0-direct`**"),
            ("c3b", "`C3b`"),
            ("c4", f"**`{c4_label}`**"),
        ):
            st = sub["solvers"][skey]
            cm = sub["common"][skey]
            p2 = sub["par2_all"][skey]
            prefix = f"**`{label}`** (`{sub['n']}`, `{sub['common_n']}`)" if first else ""
            first = False
            s_u = f"`{st['solved']}/{sub['n']}` (`{st['sat']}S/{st['unsat']}U`)"
            if skey == "c1":
                r_c0 = r_c3 = r_c1 = "—"
            elif skey == "c0direct":
                r_c0 = "`1.0000x / 1.0000x`, `1.0000x / 1.0000x`"
                r_c3 = "—"
                r_c1 = fmt_ratio_cell(sub["ratios"], "c0direct_vs_c1")
            elif skey == "c3b":
                r_c0 = fmt_ratio_cell(sub["ratios"], "c3b_vs_c0direct")
                r_c3 = "`1.0000x / 1.0000x`, `1.0000x / 1.0000x`"
                r_c1 = fmt_ratio_cell(sub["ratios"], "c3b_vs_c1")
            else:
                r_c0 = fmt_ratio_cell(sub["ratios"], "c4_vs_c0direct", bold=True)
                r_c3 = fmt_ratio_cell(sub["ratios"], "c4_vs_c3b", bold=True)
                r_c1 = fmt_ratio_cell(sub["ratios"], "c4_vs_c1", bold=True)
            lines.append(
                f"| {prefix} | {sdisp} | {s_u} | {st['timeout']} "
                f"| {fmt_num(cm['wall_am_ms'])} | {fmt_num(cm['wall_gm_ms'])} "
                f"| {fmt_num(cm['int_am_ms'])} | {fmt_num(cm['int_gm_ms'])} "
                f"| {fmt_num(cm['wall_minus_int_am_ms'])} "
                f"| {fmt_num(p2['par2_am_s'], 3)} | {fmt_num(p2['par2_gm_ms'])} "
                f"| {r_c0} | {r_c3} | {r_c1} |"
            )

    for stag, sdisp in SUITE_ORDER:
        if stag in ps and ps[stag]["n"] > 0:
            append_block(sdisp, ps[stag])
    append_block("OVERALL", ov)

    p2r = ov["par2_ratios"]
    lines += [
        "",
        "### All-N PAR-2 Pairwise Ratios",
        "",
        "| Metric | `C4 / C0-direct` | `C4 / C3b` | `C4 / C1` | `C0-direct / C1` | `C3b / C1` |",
        "|---|---:|---:|---:|---:|---:|",
        f"| **PAR-2 AM Ratio** | **`{p2r['c4_vs_c0direct']['par2_am_ratio']:.4f}x`** | `{p2r['c4_vs_c3b']['par2_am_ratio']:.4f}x` | **`{p2r['c4_vs_c1']['par2_am_ratio']:.4f}x`** | `{p2r['c0direct_vs_c1']['par2_am_ratio']:.4f}x` | `{p2r['c3b_vs_c1']['par2_am_ratio']:.4f}x` |",
        f"| **PAR-2 GM Ratio** | **`{p2r['c4_vs_c0direct']['par2_gm_ratio']:.4f}x`** | `{p2r['c4_vs_c3b']['par2_gm_ratio']:.4f}x` | **`{p2r['c4_vs_c1']['par2_gm_ratio']:.4f}x`** | `{p2r['c0direct_vs_c1']['par2_gm_ratio']:.4f}x` | `{p2r['c3b_vs_c1']['par2_gm_ratio']:.4f}x` |",
        "",
        "### Gap Attribution (Mutually Solved)",
        "",
    ]
    r_c0_c1 = ov["ratios"]["c0direct_vs_c1"]
    r_c3_c0 = ov["ratios"]["c3b_vs_c0direct"]
    r_c4_c3 = ov["ratios"]["c4_vs_c3b"]
    r_c4_c0 = ov["ratios"]["c4_vs_c0direct"]
    r_c4_c1 = ov["ratios"]["c4_vs_c1"]
    lines += [
        f"1. **C0 source & SoA data layout vs upstream Kissat (`C0-direct / C1`):** `{r_c0_c1['wall_gm']:.4f}x` Wall GM / `{r_c0_c1['int_gm']:.4f}x` Int GM / `{r_c0_c1['wall_am_ratio']:.4f}x` Wall AM",
        f"2. **`C0 -> LeanQbe.T -> PrintCpp` IR lowering (`C3b / C0-direct`):** `{r_c3_c0['wall_gm']:.4f}x` Wall GM / `{r_c3_c0['int_gm']:.4f}x` Int GM / `{r_c3_c0['wall_am_ratio']:.4f}x` Wall AM",
        f"3. **LeanQbe backend codegen vs `clang++ -O3` (`C4 / C3b`):** `{r_c4_c3['wall_gm']:.4f}x` Wall GM / `{r_c4_c3['int_gm']:.4f}x` Int GM / `{r_c4_c3['wall_am_ratio']:.4f}x` Wall AM",
        f"4. **LeanQbe total compiler overhead vs `clang -O3` on identical C0 (`C4 / C0-direct`):** `{r_c4_c0['wall_gm']:.4f}x` Wall GM / `{r_c4_c0['int_gm']:.4f}x` Int GM / `{r_c4_c0['wall_am_ratio']:.4f}x` Wall AM",
        f"5. **End-to-end verified machine code vs upstream Kissat (`C4 / C1`):** `{r_c4_c1['wall_gm']:.4f}x` Wall GM / `{r_c4_c1['int_gm']:.4f}x` Int GM / `{r_c4_c1['wall_am_ratio']:.4f}x` Wall AM",
        "",
        "### Code Size & Static Instruction Stats",
        "",
        f"| Metric | `C1` (Kissat 4.0.4) | `C0-direct` (`{mod}`) | `C3b` (`{mod}`) | `{c4_label}` |",
        "|---|---:|---:|---:|---:|",
    ]
    et = meta.get("emit_timing", {})

    def fmt_b(v):
        return "—" if v is None else f"{v:,} B"

    def fmt_i(v):
        return "—" if v is None else f"{v:,}"

    c0_em = f"{et['c0_extract_ms'] / 1000.0:.2f} s" if "c0_extract_ms" in et else "—"
    c3_em = f"{et['cpp_emit_ms'] / 1000.0:.2f} s" if "cpp_emit_ms" in et else "—"
    c4_em = f"{et['c4_emit_ms'] / 1000.0:.2f} s" if "c4_emit_ms" in et else "—"

    lines += [
        f"| **Emission Wall Time** | — | {c0_em} | {c3_em} | {c4_em} |",
        f"| **Object `.text` Size** | — | {fmt_b(sizes['c0direct']['obj_text_bytes'])} | {fmt_b(sizes['c3b']['obj_text_bytes'])} | {fmt_b(sizes['c4']['obj_text_bytes'])} |",
        f"| **Linked Binary `.text` Size** | {fmt_b(sizes['c1']['bin_text_bytes'])} | {fmt_b(sizes['c0direct']['bin_text_bytes'])} | {fmt_b(sizes['c3b']['bin_text_bytes'])} | {fmt_b(sizes['c4']['bin_text_bytes'])} |",
        f"| **Assembly Size (`.s`)** | — | — | — | {fmt_b(sizes['c4'].get('asm_bytes'))} |",
        f"| **Static Non-NOP Insns** | {fmt_i(sizes['c1']['non_nop_insns'])} | {fmt_i(sizes['c0direct']['non_nop_insns'])} | {fmt_i(sizes['c3b']['non_nop_insns'])} | {fmt_i(sizes['c4']['non_nop_insns'])} |",
        "",
    ]
    return "\n".join(lines)


def get_host_info(cc, cxx):
    cpu_model = "unknown"
    try:
        for line in pathlib.Path("/proc/cpuinfo").read_text().splitlines():
            if line.startswith("model name"):
                cpu_model = line.split(":", 1)[1].strip()
                break
    except OSError:
        pass
    try:
        git_rev = subprocess.check_output(
            ["git", "rev-parse", "--short=12", "HEAD"], cwd=str(ROOT), text=True
        ).strip()
    except Exception:
        git_rev = "unknown"

    def first_line(cmd):
        try:
            out = subprocess.check_output(cmd, text=True, stderr=subprocess.STDOUT)
            return out.splitlines()[0].strip() if out.splitlines() else "unknown"
        except Exception:
            return "unknown"

    la = os.getloadavg()
    return {
        "cpu_model": cpu_model,
        "nproc": os.cpu_count() or 1,
        "git_rev": git_rev,
        "cc_version": first_line([cc, "--version"]),
        "cxx_version": first_line([cxx, "--version"]),
        "start_loadavg": f"{la[0]:.2f}, {la[1]:.2f}, {la[2]:.2f}",
    }


def format_extensions_markdown(payload):
    meta = payload["meta"]
    fid_ov = payload["fidelity_overall"]
    fid_ps = payload["fidelity_per_suite"]
    opt_ov = payload["opt_overall"]
    opt_ps = payload["opt_per_suite"]
    ext_ov = payload["overall"]
    fid_mod = meta["fid_module"]
    opt_mod = meta["opt_module"]
    lines = [
        f"# [NON-FIDELITY SOLVER EXTENSION] Stage-1 Extensions Benchmark: `{opt_mod}` vs `{fid_mod}` & `C1`",
        "",
        f"- **Date (UTC):** {meta['timestamp_utc']}",
        f"- **Benchmark Type:** `{meta['benchmark_type']}` (`is_fidelity=False`, `is_solver_extension=True`)",
        f"- **Git commit:** `{meta['git_rev']}`",
        f"- **Fidelity Baseline:** `{fid_mod}` (`{meta['fid_fn_count']}` fns, `{meta['fid_policy_desc']}`)",
        f"- **Extension Solver:** `{opt_mod}` (`{meta['opt_fn_count']}` fns, `{meta['opt_policy_desc']}`)",
        f"- **Parameters:** `{fid_ov['n']}` CNFs, timeout `{meta['timeout_s']:.1f}s`, floor `{meta['floor_ms']:.1f}ms`, `--jobs {meta['jobs']}`, fuel `{meta['fuel']:,}`.",
        f"- **Verification:** `{payload['soundness']['sound_errs']}` soundness errors, `{len(payload['soundness']['disagreements'])}` disagreements, Fidelity parity `{payload['parity']['fidelity']['ok']}/{payload['parity']['fidelity']['total']}`, Opt parity `{payload['parity']['opt']['ok']}/{payload['parity']['opt']['total']}`.",
        "",
    ]

    def emit_solver_table(title, c4_name, ov, ps, c0k, c3k, c4k):
        lines.extend([
            f"## {title}",
            "",
            "| Suite (`N`, common) | Engine | Solved (`S/U`) | TO | Wall GM (ms) | Int GM (ms) | PAR-2 AM (s) | `vs C0-direct` (W-GM/AM, I-GM/AM) | `vs C3b` (W-GM/AM, I-GM/AM) | `vs C1` (W-GM/AM, I-GM/AM) |",
            "|---|---|---|---:|---:|---:|---:|---|---|---|",
        ])

        def app(lbl, sub):
            first = True
            for skey, sdisp in (("c1", "`C1`"), (c0k, "**`C0-direct`**"), (c3k, "`C3b`"), (c4k, f"**`{c4_name}`**")):
                st, cm, p2 = sub["solvers"][skey], sub["common"][skey], sub["par2_all"][skey]
                pfx = f"**`{lbl}`** (`{sub['n']}`, `{sub['common_n']}`)" if first else ""
                first = False
                s_u = f"`{st['solved']}/{sub['n']}` (`{st['sat']}S/{st['unsat']}U`)"
                if skey == "c1":
                    r_c0 = r_c3 = r_c1 = "—"
                elif skey == c0k:
                    r_c0, r_c3 = "`1.0000x / 1.0000x`, `1.0000x / 1.0000x`", "—"
                    r_c1 = fmt_ratio_cell(sub["ratios"], f"{c0k}_vs_c1")
                elif skey == c3k:
                    r_c0 = fmt_ratio_cell(sub["ratios"], f"{c3k}_vs_{c0k}")
                    r_c3 = "`1.0000x / 1.0000x`, `1.0000x / 1.0000x`"
                    r_c1 = fmt_ratio_cell(sub["ratios"], f"{c3k}_vs_c1")
                else:
                    r_c0 = fmt_ratio_cell(sub["ratios"], f"{c4k}_vs_{c0k}", bold=True)
                    r_c3 = fmt_ratio_cell(sub["ratios"], f"{c4k}_vs_{c3k}", bold=True)
                    r_c1 = fmt_ratio_cell(sub["ratios"], f"{c4k}_vs_c1", bold=True)
                lines.append(
                    f"| {pfx} | {sdisp} | {s_u} | {st['timeout']} "
                    f"| {fmt_num(cm['wall_gm_ms'])} | {fmt_num(cm['int_gm_ms'])} "
                    f"| {fmt_num(p2['par2_am_s'], 3)} | {r_c0} | {r_c3} | {r_c1} |"
                )

        for stag, sdisp in SUITE_ORDER:
            if stag in ps and ps[stag]["n"] > 0:
                app(sdisp, ps[stag])
        app("OVERALL", ov)
        lines.append("")

    emit_solver_table(f"Part A: Compiler Benchmark Baseline (`{fid_mod}`)", f"C4 ({fid_mod})", fid_ov, fid_ps, "c0direct_fid", "c3b_fid", "c4_fid")
    emit_solver_table(f"Part B: Beyond-Upstream Solver Extensions (`{opt_mod}`)", f"C4 ({opt_mod})", opt_ov, opt_ps, "c0direct_opt", "c3b_opt", "c4_opt")

    er = ext_ov["ratios"]
    lines.extend([
        "## Separated Attribution (Compiler Overhead vs. Algorithmic Gain)",
        "",
        f"1. **Compiler overhead on `{fid_mod}` (`C4 / C0-direct`):** `{er['c4_fid_vs_c0direct_fid']['wall_gm']:.4f}x` Wall GM / `{er['c4_fid_vs_c0direct_fid']['int_gm']:.4f}x` Int GM (`C4 / C3b`: `{er['c4_fid_vs_c3b_fid']['wall_gm']:.4f}x`)",
        f"2. **Compiler overhead on `{opt_mod}` (`C4 / C0-direct`):** `{er['c4_opt_vs_c0direct_opt']['wall_gm']:.4f}x` Wall GM / `{er['c4_opt_vs_c0direct_opt']['int_gm']:.4f}x` Int GM (`C4 / C3b`: `{er['c4_opt_vs_c3b_opt']['wall_gm']:.4f}x`)",
        f"3. **Pure algorithmic gain (`C0-direct({opt_mod}) / C0-direct({fid_mod})`):** `{er['c0direct_opt_vs_c0direct_fid']['wall_gm']:.4f}x` Wall GM / `{er['c0direct_opt_vs_c0direct_fid']['int_gm']:.4f}x` Int GM",
        f"4. **Pure algorithmic gain on verified code (`C4({opt_mod}) / C4({fid_mod})`):** `{er['c4_opt_vs_c4_fid']['wall_gm']:.4f}x` Wall GM / `{er['c4_opt_vs_c4_fid']['int_gm']:.4f}x` Int GM",
        f"5. **End-to-end vs upstream Kissat 4.0.4 (`C4({opt_mod}) / C1`):** `{er['c4_opt_vs_c1']['wall_gm']:.4f}x` Wall GM / `{er['c4_opt_vs_c1']['int_gm']:.4f}x` Int GM",
        "",
    ])
    return "\n".join(lines)


def run_extensions_mode(args, entries, manifest_path, c1_bin, out_json, out_md):
    fid_spec = resolve_module_spec(args.fid_module)
    opt_spec = resolve_module_spec(args.opt_module)
    print(
        f"[NON-FIDELITY SOLVER EXTENSION] Running separated extensions mode: "
        f"{fid_spec['module']} vs {opt_spec['module']} & C1",
        file=sys.stderr, flush=True,
    )
    temp_dir_obj = None
    if args.build_dir:
        bdir = pathlib.Path(args.build_dir)
    else:
        temp_dir_obj = tempfile.TemporaryDirectory(prefix="kissat-ext-stage1-")
        bdir = pathlib.Path(temp_dir_obj.name)
    try:
        fid_bins, fid_sizes, fid_timing = build_corners(
            fid_spec, bdir / "fid", c1_bin, args.cc, args.cxx, args.skip_lake_build, args.reuse_bins
        )
        opt_bins, opt_sizes, opt_timing = build_corners(
            opt_spec, bdir / "opt", c1_bin, args.cc, args.cxx, args.skip_lake_build, args.reuse_bins
        )
        host_info = get_host_info(args.cc, args.cxx)
        bins = {
            "c1": str(c1_bin),
            "c0direct_fid": fid_bins["c0direct"], "c3b_fid": fid_bins["c3b"], "c4_fid": fid_bins["c4"],
            "c0direct_opt": opt_bins["c0direct"], "c3b_opt": opt_bins["c3b"], "c4_opt": opt_bins["c4"],
        }
        solvers = list(bins)
        fid_c0 = ("c0direct_fid", "c3b_fid", "c4_fid")
        opt_c0 = ("c0direct_opt", "c3b_opt", "c4_opt")

        def eval_one(idx_e):
            i, e = idx_e
            shift = i % len(solvers)
            order = solvers[shift:] + solvers[:shift]
            row = {}
            for s in order:
                if s == "c1":
                    row[s] = run_c1_trial(bins[s], e, e["cnf_path"], args.timeout)
                else:
                    row[s] = run_c0_trial(bins[s], e, e["cnf_path"], args.timeout, args.work_mb, args.fuel)
            return i, row

        rows = [None] * len(entries)
        t0 = time.perf_counter()
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futs = {ex.submit(eval_one, ie): ie[0] for ie in enumerate(entries)}
            done = 0
            for fut in concurrent.futures.as_completed(futs):
                i, row = fut.result()
                rows[i] = row
                done += 1
                e = entries[i]
                print(
                    f"[{done:3d}/{len(entries)}] {e['id'][:30]:30s} | "
                    f"c1={row['c1']['wall_ms']:7.1f} fid_c4={row['c4_fid']['internal_ms']:7.1f} "
                    f"opt_c4={row['c4_opt']['internal_ms']:7.1f}",
                    flush=True,
                )
        elapsed_s = time.perf_counter() - t0
    finally:
        if temp_dir_obj is not None:
            temp_dir_obj.cleanup()

    def check_c0_parity(group_solvers, ref_key):
        diffs_list, tot = [], 0
        for e, r in zip(entries, rows):
            if all((not r[s].get("timed_out")) and r[s]["status"] in (10, 20) for s in group_solvers):
                tot += 1
                diffs = {
                    k: {s: r[s].get(k) for s in group_solvers}
                    for k in ALL_TELEM_KEYS
                    if len({r[s].get(k) for s in group_solvers}) > 1
                }
                if diffs:
                    diffs_list.append({"id": e["id"], "ref": ref_key, "diffs": diffs})
        return tot, diffs_list

    fid_par_n, fid_diffs = check_c0_parity(fid_c0, "c0direct_fid")
    opt_par_n, opt_diffs = check_c0_parity(opt_c0, "c0direct_opt")
    disagreements, sound_errs = [], 0
    for e, r in zip(entries, rows):
        for s in solvers:
            if not r[s].get("model_ok", True) or not r[s].get("verdict_ok", True):
                sound_errs += 1
        sts = {s: r[s]["status"] for s in solvers if (not r[s].get("timed_out")) and r[s]["status"] in (10, 20)}
        if len(set(sts.values())) > 1:
            disagreements.append({"id": e["id"], "statuses": sts})

    fid_pairs = [("c3b_fid", "c0direct_fid"), ("c4_fid", "c0direct_fid"), ("c0direct_fid", "c1"),
                 ("c3b_fid", "c1"), ("c4_fid", "c1"), ("c4_fid", "c3b_fid")]
    opt_pairs = [("c3b_opt", "c0direct_opt"), ("c4_opt", "c0direct_opt"), ("c0direct_opt", "c1"),
                 ("c3b_opt", "c1"), ("c4_opt", "c1"), ("c4_opt", "c3b_opt")]
    ext_pairs = fid_pairs + opt_pairs + [
        ("c0direct_opt", "c0direct_fid"), ("c3b_opt", "c3b_fid"), ("c4_opt", "c4_fid"),
    ]
    fid_ps, opt_ps = {}, {}
    for stag, _ in SUITE_ORDER:
        sub = [rows[i] for i, e in enumerate(entries) if stag in e.get("suites", [e.get("suite")])]
        if sub:
            fid_ps[stag] = summarize_subset(sub, ["c1", *fid_c0], fid_pairs, args.timeout, args.floor_ms)
            opt_ps[stag] = summarize_subset(sub, ["c1", *opt_c0], opt_pairs, args.timeout, args.floor_ms)
    fid_ov = summarize_subset(rows, ["c1", *fid_c0], fid_pairs, args.timeout, args.floor_ms)
    opt_ov = summarize_subset(rows, ["c1", *opt_c0], opt_pairs, args.timeout, args.floor_ms)
    ext_ov = summarize_subset(rows, solvers, ext_pairs, args.timeout, args.floor_ms)

    la_end = os.getloadavg()
    payload = {
        "benchmark_type": "solver_extensions",
        "is_fidelity": False,
        "is_solver_extension": True,
        "meta": {
            "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M:%SZ"),
            "benchmark_type": "solver_extensions",
            "is_fidelity": False,
            "is_solver_extension": True,
            "fid_module": fid_spec["module"],
            "opt_module": opt_spec["module"],
            "fid_fn_count": fid_timing.get("fn_count"),
            "opt_fn_count": opt_timing.get("fn_count"),
            "fid_policy_desc": fid_spec["policy_desc"],
            "opt_policy_desc": opt_spec["policy_desc"],
            "manifest": str(manifest_path),
            "c1_bin": str(c1_bin),
            "jobs": args.jobs,
            "timeout_s": args.timeout,
            "floor_ms": args.floor_ms,
            "fuel": args.fuel,
            "elapsed_s": round(elapsed_s, 2),
            "end_loadavg": f"{la_end[0]:.2f}, {la_end[1]:.2f}, {la_end[2]:.2f}",
            **host_info,
        },
        "code_sizes": {"fidelity": fid_sizes, "opt": opt_sizes},
        "parity": {
            "fidelity": {"total": fid_par_n, "ok": fid_par_n - len(fid_diffs), "diffs_count": len(fid_diffs), "diffs": fid_diffs},
            "opt": {"total": opt_par_n, "ok": opt_par_n - len(opt_diffs), "diffs_count": len(opt_diffs), "diffs": opt_diffs},
        },
        "soundness": {"sound_errs": sound_errs, "disagreements": disagreements},
        "overall": ext_ov,
        "fidelity_overall": fid_ov,
        "fidelity_per_suite": fid_ps,
        "opt_overall": opt_ov,
        "opt_per_suite": opt_ps,
        "results": [
            {"id": e["id"], "suite": e.get("suite"), "expected": e.get("expected_verdict"), "solvers": r}
            for e, r in zip(entries, rows)
        ],
    }
    md_text = format_extensions_markdown(payload)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_md.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2) + "\n")
    out_md.write_text(md_text + "\n")
    print(f"JSON: {out_json}\nMD  : {out_md}")
    if sound_errs > 0 or disagreements or fid_diffs or opt_diffs:
        raise SystemExit(
            f"FAIL: soundness/parity audit failed "
            f"(sound_errs={sound_errs}, disagreements={len(disagreements)}, "
            f"fid_diffs={len(fid_diffs)}, opt_diffs={len(opt_diffs)})"
        )


def main():
    ap = argparse.ArgumentParser(
        description="Build and run reproducible 4-way Stage-1 (140-CNF) Kissat benchmark."
    )
    ap.add_argument(
        "--module", default=None,
        help="Solver module (default: KissatFidelity if present, else Plain; "
             "supports KissatFidelity, KissatM8Opt, Plain)",
    )
    ap.add_argument(
        "--mode", choices=["compiler", "extensions"], default="compiler",
        help="Benchmark mode: 'compiler' (default, tags compiler_evaluation) or 'extensions' (Fidelity vs M8Opt dual report)",
    )
    ap.add_argument("--allow-solver-extensions", action="store_true",
                    help="Acknowledge running --mode compiler on a non-fidelity solver extension")
    ap.add_argument("--fid-module", default="KissatFidelity", help="Fidelity baseline module for --mode extensions")
    ap.add_argument("--opt-module", default="KissatM8Opt", help="Extension solver module for --mode extensions")
    ap.add_argument("--jobs", type=int, default=8, help="Parallel worker count (default: 8)")
    ap.add_argument("--timeout", type=float, default=30.0, help="Per-CNF timeout in seconds (default: 30.0)")
    ap.add_argument("--floor-ms", type=float, default=20.0, help="Geometric mean timing floor in ms (default: 20.0)")
    ap.add_argument("--fuel", type=int, default=2000000000, help="C0 solver fuel budget (default: 2000000000)")
    ap.add_argument("--work-mb", type=int, default=None, help="Override workspace MiB (default: manifest per-CNF min_work_mb)")
    ap.add_argument("--manifest", default=None, help="Path to Stage-1 manifest JSON (or STAGE1_MANIFEST)")
    ap.add_argument("--c1-bin", default=None, help="Path to upstream Kissat 4.0.4 binary (or KISSAT_C1_BIN)")
    ap.add_argument("--out-json", default=None, help="Output JSON report path")
    ap.add_argument("--out-md", default=None, help="Output Markdown report path")
    ap.add_argument("--build-dir", default=None, help="Persistent build directory (default: temporary directory)")
    ap.add_argument("--reuse-bins", action="store_true", help="Reuse prebuilt binaries in --build-dir if present")
    ap.add_argument("--skip-lake-build", action="store_true", help="Skip `lake build` step")
    ap.add_argument("--suite", choices=["pv35", "hard24", "sv21", "quick60"], default=None, help="Optional single-suite filter")
    ap.add_argument("--limit", type=int, default=None, help="Optional cap on number of CNFs (for smoke tests)")
    ap.add_argument("--cc", default=os.environ.get("CC", "clang"), help="C compiler (default: clang)")
    ap.add_argument("--cxx", default=os.environ.get("CXX", "clang++"), help="C++ compiler (default: clang++)")
    args = ap.parse_args()

    manifest_path = resolve_manifest(args.manifest)
    c1_bin = resolve_c1_bin(args.c1_bin)
    man = json.loads(manifest_path.read_text())
    entries = list(man["benchmarks"])
    if args.suite:
        entries = [e for e in entries if args.suite in e.get("suites", [e.get("suite")])]
    if args.limit is not None:
        entries = entries[: args.limit]
    if not entries:
        raise SystemExit("ERROR: no benchmarks selected from manifest.")
    missing_cnfs = [e["cnf_path"] for e in entries if not os.path.isfile(e["cnf_path"])]
    if missing_cnfs:
        raise SystemExit(f"ERROR: {len(missing_cnfs)} missing CNF files, first: {missing_cnfs[0]}")

    if args.mode == "extensions":
        out_json = pathlib.Path(args.out_json or "/tmp/kissat_4way_stage1_extensions.json")
        out_md = pathlib.Path(args.out_md or "/tmp/kissat_4way_stage1_extensions.md")
        return run_extensions_mode(args, entries, manifest_path, c1_bin, out_json, out_md)

    spec = resolve_module_spec(args.module or default_module())
    ext_warning = spec["is_solver_extension"] and (not args.allow_solver_extensions)
    if ext_warning:
        print(
            f"[NON-FIDELITY SOLVER EXTENSION]\n"
            f"[WARNING] {spec['module']} includes beyond-upstream solver heuristics; ratios vs C1 conflate "
            f"solver algorithm and compiler codegen! Use --module KissatFidelity for compiler benchmarks.",
            file=sys.stderr, flush=True,
        )
    out_json = pathlib.Path(args.out_json or f"/tmp/kissat_4way_stage1_{spec['tag']}.json")
    out_md = pathlib.Path(args.out_md or f"/tmp/kissat_4way_stage1_{spec['tag']}.md")

    temp_dir_obj = None
    if args.build_dir:
        bdir = pathlib.Path(args.build_dir)
    else:
        temp_dir_obj = tempfile.TemporaryDirectory(prefix=f"kissat-4way-{spec['tag']}-")
        bdir = pathlib.Path(temp_dir_obj.name)

    try:
        bins, code_sizes, emit_timing = build_corners(
            spec, bdir, c1_bin, args.cc, args.cxx, args.skip_lake_build, args.reuse_bins
        )
        host_info = get_host_info(args.cc, args.cxx)

        solvers = ["c1", "c0direct", "c3b", "c4"]
        c0_solvers = ["c0direct", "c3b", "c4"]
        print(
            f"== Evaluating {len(entries)} Stage-1 CNFs across 4 corners "
            f"(jobs={args.jobs}, timeout={args.timeout:.1f}s, floor={args.floor_ms:.1f}ms, "
            f"loadavg={host_info['start_loadavg']}) ==",
            flush=True,
        )

        def eval_one(idx_e):
            i, e = idx_e
            shift = i % len(solvers)
            order = solvers[shift:] + solvers[:shift]
            row = {}
            for s in order:
                if s == "c1":
                    row[s] = run_c1_trial(bins[s], e, e["cnf_path"], args.timeout)
                else:
                    row[s] = run_c0_trial(
                        bins[s], e, e["cnf_path"], args.timeout, args.work_mb, args.fuel
                    )
            return i, row

        rows = [None] * len(entries)
        t0 = time.perf_counter()
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            futs = {ex.submit(eval_one, ie): ie[0] for ie in enumerate(entries)}
            done = 0
            for fut in concurrent.futures.as_completed(futs):
                i, row = fut.result()
                rows[i] = row
                done += 1
                e = entries[i]
                st_ok = all(
                    (not row[s].get("timed_out")) and row[s]["status"] in (10, 20)
                    for s in c0_solvers
                )
                par_ok = st_ok and all(
                    row[s].get(k) == row["c0direct"].get(k)
                    for s in ("c3b", "c4") for k in ALL_TELEM_KEYS
                )
                par_tag = "OK" if par_ok else ("TO" if not st_ok else "DIFF")
                print(
                    f"[{done:3d}/{len(entries)}] {e['id'][:32]:32s} | "
                    f"c1={row['c1']['wall_ms']:7.1f} c0d={row['c0direct']['internal_ms']:7.1f} "
                    f"c3b={row['c3b']['internal_ms']:7.1f} c4={row['c4']['internal_ms']:7.1f} "
                    f"| par={par_tag}",
                    flush=True,
                )
        elapsed_s = time.perf_counter() - t0
    finally:
        if temp_dir_obj is not None:
            temp_dir_obj.cleanup()

    parity_diffs = []
    parity_n = 0
    disagreements = []
    sound_errs = 0
    for e, r in zip(entries, rows):
        for s in solvers:
            if not r[s].get("model_ok", True) or not r[s].get("verdict_ok", True):
                sound_errs += 1
        sts = {
            s: r[s]["status"]
            for s in solvers
            if (not r[s].get("timed_out")) and r[s]["status"] in (10, 20)
        }
        if len(set(sts.values())) > 1:
            disagreements.append({"id": e["id"], "statuses": sts})
        if all((not r[s].get("timed_out")) and r[s]["status"] in (10, 20) for s in c0_solvers):
            parity_n += 1
            diffs = {}
            for k in ALL_TELEM_KEYS:
                vals = {s: r[s].get(k) for s in c0_solvers}
                if len(set(vals.values())) > 1:
                    diffs[k] = vals
            if diffs:
                parity_diffs.append({"id": e["id"], "diffs": diffs})

    pairs = [
        ("c3b", "c0direct"), ("c4", "c0direct"),
        ("c0direct", "c1"), ("c3b", "c1"),
        ("c4", "c1"), ("c4", "c3b"),
    ]
    per_suite = {}
    for stag, _ in SUITE_ORDER:
        sub_rows = [
            rows[i] for i, e in enumerate(entries)
            if stag in e.get("suites", [e.get("suite")])
        ]
        if sub_rows:
            per_suite[stag] = summarize_subset(sub_rows, solvers, pairs, args.timeout, args.floor_ms)
    overall = summarize_subset(rows, solvers, pairs, args.timeout, args.floor_ms)

    la_end = os.getloadavg()
    payload = {
        "benchmark_type": "compiler_evaluation",
        "is_fidelity": spec["is_fidelity"],
        "is_solver_extension": spec["is_solver_extension"],
        "meta": {
            "timestamp_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%d %H:%M:%SZ"),
            "benchmark_type": "compiler_evaluation",
            "is_fidelity": spec["is_fidelity"],
            "is_solver_extension": spec["is_solver_extension"],
            "ext_warning": ext_warning,
            "module": spec["module"],
            "fn_count": emit_timing.get("fn_count"),
            "dir_count": emit_timing.get("dir_count"),
            "policy_desc": spec["policy_desc"],
            "certified_x64": spec["certified_x64"],
            "manifest": str(manifest_path),
            "c1_bin": str(c1_bin),
            "jobs": args.jobs,
            "timeout_s": args.timeout,
            "floor_ms": args.floor_ms,
            "fuel": args.fuel,
            "elapsed_s": round(elapsed_s, 2),
            "end_loadavg": f"{la_end[0]:.2f}, {la_end[1]:.2f}, {la_end[2]:.2f}",
            "emit_timing": emit_timing,
            **host_info,
        },
        "code_sizes": code_sizes,
        "parity": {"total": parity_n, "diffs_count": len(parity_diffs), "diffs": parity_diffs},
        "soundness": {"sound_errs": sound_errs, "disagreements": disagreements},
        "overall": overall,
        "per_suite": per_suite,
        "results": [
            {
                "id": e["id"],
                "suite": e.get("suite"),
                "expected": e.get("expected_verdict"),
                "solvers": r,
            }
            for e, r in zip(entries, rows)
        ],
    }

    md_text = format_markdown(payload)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_md.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2) + "\n")
    out_md.write_text(md_text + "\n")

    print(
        f"\nCompleted in {elapsed_s:.1f}s | 3-way C0 parity={parity_n - len(parity_diffs)}/{parity_n} "
        f"(diffs={len(parity_diffs)}) | sound_errs={sound_errs} disagreements={len(disagreements)}"
    )
    print(f"JSON: {out_json}")
    print(f"MD  : {out_md}")

    if sound_errs > 0 or disagreements or parity_diffs:
        raise SystemExit(
            f"FAIL: soundness/parity audit failed "
            f"(sound_errs={sound_errs}, disagreements={len(disagreements)}, parity_diffs={len(parity_diffs)})"
        )


if __name__ == "__main__":
    main()
