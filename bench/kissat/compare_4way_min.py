#!/usr/bin/env python3
"""Minimal auditable 4-way Kissat benchmark: C1 vs C0-direct vs C3b vs C4 (x86-64)."""
import argparse, json, math, os, pathlib, shutil, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parents[2]
SOLVERS_JSON = ROOT / "bench/kissat/solvers.json"
MODS = {
    "KissatFidelity": (
        "fidelity", "FullFidelityAssembly", "FullFidelityAssembly.fidModule",
        "LeanQbe.T.Examples.Kissat.FullFidelityInl", "FullFidelityInl.fidInlFns",
    ),
    "KissatM8Opt": (
        "m8opt", "FullM8OptAssembly", "FullM8OptAssembly.m8OptModule",
        "LeanQbe.T.Examples.Kissat.FullM8OptInl", "FullM8OptInl.m8OptInlFns",
    ),
    "Plain": ("plain", "Plain", "Plain.plainModule", None, "Plain.plainFns"),
    "FullM5": ("m5", "FullM5", "FullM5.m5Module", "LeanQbe.T.MainInline",
               "((FullM5.m5Module).optInlinePolicy InlinePolicy.b5).fns"),
    "FullM6": ("m6", "FullM6", "FullM6.m6Module", "LeanQbe.T.Examples.Kissat.FullM6Inl", "FullM6Inl.m6InlFns"),
    "FullM7Plus": ("m7plus", "FullM7PlusAssembly", "FullM7Plus.m7PlusModule",
                   "LeanQbe.T.Examples.Kissat.FullM7PlusInl", "FullM7PlusInl.m7PlusInlFns"),
    "FullM7Fidelity": ("m7fidelity", "FullM7FidelityAssembly", "FullM7Fidelity.m7FidelityModule",
                       "LeanQbe.T.Examples.Kissat.FullM7FidelityInl", "FullM7FidelityInl.m7FidInlFns"),
}
MOD_ALIASES = {
    **{k.lower(): k for k in MODS},
    "fullfidelity": "KissatFidelity", "fidelity": "KissatFidelity", "fid": "KissatFidelity",
    "fullm8opt": "KissatM8Opt", "m8opt": "KissatM8Opt", "opt": "KissatM8Opt",
    "fullm8": "KissatM8Opt", "m8": "KissatM8Opt",
    "kissatplain": "Plain",
    "m5": "FullM5", "m6": "FullM6",
    "m7plus": "FullM7Plus", "m7fidelity": "FullM7Fidelity", "m7fid": "FullM7Fidelity",
}
EXTENSION_MODS = {"KissatM8Opt", "FullM7Plus"}
ENGINES = ("c1", "c0direct", "c3b", "c4")
EXT_ENGINES = ("c1", "c0_fid", "c4_fid", "c0_opt", "c4_opt")


def default_module():
    if (ROOT / "LeanQbe/T/Amd64/KissatFidelity.lean").is_file() and (
        ROOT / "LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean"
    ).is_file():
        return "KissatFidelity"
    return "FullM7Fidelity"


def resolve_module(raw_name):
    key = MOD_ALIASES.get(raw_name.strip().lower())
    if key is None:
        raise SystemExit(f"ERROR: unknown --module '{raw_name}' (expected one of: {', '.join(MODS)})")
    return key


def is_solver_extension(mod):
    if SOLVERS_JSON.is_file():
        reg = json.loads(SOLVERS_JSON.read_text(encoding="utf-8"))
        if mod in reg:
            return bool(reg[mod].get("is_solver_extension", False))
    return mod in EXTENSION_MODS


def resolve_emit_exprs(mod):
    c0_tgt, lean_file, mod_expr, extra_imp, fns_expr = MODS[mod]
    kdir = ROOT / "LeanQbe/T/Examples/Kissat"
    if extra_imp:
        short = extra_imp.split(".")[-1]
        if extra_imp.startswith("LeanQbe.T.Examples.Kissat.") and not (kdir / f"{short}.lean").is_file():
            pol_mod = (
                "FullFidelityInlPolicy" if mod == "KissatFidelity"
                else ("FullM8InlPolicy" if mod == "KissatM8Opt" else None)
            )
            pol_sym = (
                "FullFidelityInlPolicy.fidInlPolicy" if mod == "KissatFidelity"
                else ("FullM8InlPolicy.m8InlPolicy" if mod == "KissatM8Opt" else None)
            )
            if pol_mod and (kdir / f"{pol_mod}.lean").is_file():
                return c0_tgt, lean_file, mod_expr, [
                    "LeanQbe.T.MainInline", f"LeanQbe.T.Examples.Kissat.{pol_mod}"
                ], f"(({mod_expr}).optInlinePolicy {pol_sym}).fns"
            return c0_tgt, lean_file, mod_expr, [], f"({mod_expr}).fns"
        return c0_tgt, lean_file, mod_expr, [extra_imp], fns_expr
    return c0_tgt, lean_file, mod_expr, [], fns_expr

def sh(cmd, timeout=600):
    print("$", " ".join(map(str, cmd)), flush=True)
    subprocess.run(["timeout", "-k", "5s", f"{timeout}s", *map(str, cmd)], cwd=ROOT, check=True)

def text_bytes(path):
    out = subprocess.check_output(["timeout", "30s", "size", "-A", str(path)], text=True)
    return next(int(p[1]) for l in out.splitlines() if (p := l.split()) and p[0] == ".text")

def verify_dimacs_model(cnf_path, stdout):
    vals = {abs(x): x > 0 for l in stdout.splitlines() if l.startswith("v ")
            for t in l[2:].split() if (x := int(t)) != 0}
    assert vals, f"no model lines for {cnf_path}"
    cur = []
    for raw in open(cnf_path, "rb"):
        s = raw.decode("ascii", errors="replace").strip()
        if not s or s[0] in "cp": continue
        if s[0] == "%": break
        for t in s.split():
            if t == "%": break
            lit = int(t)
            if lit == 0:
                assert any(vals.get(abs(l)) == (l > 0) for l in cur), f"unsat clause in {cnf_path}"
                cur = []
            else:
                cur.append(lit)
    assert not cur or any(vals.get(abs(l)) == (l > 0) for l in cur), f"unsat tail in {cnf_path}"

def build_solver_bins(tmp, mod, drv, skip_lake, tag_prefix=""):
    c0_tgt, lean_file, mod_expr, extra_imps, fns_expr = resolve_emit_exprs(mod)
    pfx = f"{tag_prefix}_" if tag_prefix else ""
    if not skip_lake:
        sh(["lake", "build", "--wfail", f"LeanQbe.T.Examples.Kissat.{lean_file}", *extra_imps,
            "LeanQbe.T.PrintCpp", "LeanQbe.T.Opt", "LeanQbe.T.Driver",
            "LeanQbe.T.Amd64.Targ", "LeanQbe.T.Amd64.PrintATTAlign"], 1800)
    c_path = tmp / f"{pfx}c0.c"
    o_path = tmp / f"{pfx}c0.o"
    c0_bin = tmp / f"{pfx}c0direct"
    c0_flags = ["-std=c99", "-O3", "-fwrapv", "-fno-strict-aliasing"]
    if c0_tgt == "plain":
        c0_flags.append("-Wno-parentheses")
    sh([sys.executable, "-B", ROOT / "bench/kissat/extract_c0_direct.py",
        "--target", c0_tgt, "--out", c_path, "--check-fns", "lean"], 120)
    sh(["clang", *c0_flags, f"-I{ROOT/'LeanQbe/T/Frontend/C0'}", "-c", c_path, "-o", o_path], 180)
    sh(["clang", o_path, drv, "-o", c0_bin], 120)
    imp_lines = "".join(f"import {m}\n" for m in extra_imps)
    (tmp / f"{pfx}Emit.lean").write_text(
        f"import LeanQbe.T.Examples.Kissat.{lean_file}\n{imp_lines}"
        "import LeanQbe.T.PrintCpp\nimport LeanQbe.T.Opt\nimport LeanQbe.T.Driver\n"
        "import LeanQbe.T.Amd64.Targ\nimport LeanQbe.T.Amd64.PrintATTAlign\n"
        "open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Amd64 LeanQbe.T.Examples.Kissat\n"
        "def main (args : List String) : IO Unit := do\n"
        "  let [hpp, asm] := args | throw (IO.userError \"usage: <hpp> <asm>\")\n"
        f"  match ppTModule {mod_expr} with\n"
        "  | .ok s => IO.FS.writeFile hpp s | .error e => throw (IO.userError e)\n"
        f"  let fns := {fns_expr}\n"
        "  match Driver.compileFns x64Target.toIsa x64LegalTarget fns with\n"
        "  | .ok d => IO.FS.writeFile asm (Driver.emitAsm (fun c => toATTAligned c ++ \"\\n\") fns d)\n"
        "  | .error e => throw (IO.userError e)\n")
    hpp_path, s_path = tmp / f"{pfx}gen.hpp", tmp / f"{pfx}c4.s"
    sh(["lake", "env", "lean", "--run", tmp / f"{pfx}Emit.lean", hpp_path, s_path], 600)
    c3b_cpp = tmp / f"{pfx}c3b.cpp"
    c3b_cpp.write_text(
        f'#include <cstdint>\n#include "tqbe_rt.hpp"\nnamespace tqbe_gen {{\n#include "{hpp_path.name}"\n}}\n'
        'extern "C" uint64_t kissat_solve_bytes(const uint8_t *c, uint64_t cl, uint8_t *w, uint64_t wl, uint64_t f) {\n'
        '  ::tqbe::Mem m; return tqbe_gen::kissat_solve_bytes(m, ::tqbe::bits<64>((uintptr_t)c), '
        '::tqbe::bits<64>(cl), ::tqbe::bits<64>((uintptr_t)w), ::tqbe::bits<64>(wl), ::tqbe::bits<64>(f)).word(0); }\n')
    c3b_bin, c4_bin = tmp / f"{pfx}c3b", tmp / f"{pfx}c4"
    sh(["clang++", "-std=c++20", "-O3", "-DTQBE_NATIVE_MEM",
        f"-I{ROOT/'LeanQbe/T/Runtime'}", f"-I{tmp}", "-c", c3b_cpp, "-o", tmp / f"{pfx}c3b.o"], 300)
    sh(["clang++", tmp / f"{pfx}c3b.o", drv, "-o", c3b_bin], 120)
    sh(["gcc", "-c", s_path, "-o", tmp / f"{pfx}c4.o"], 120)
    sh(["gcc", "-no-pie", tmp / f"{pfx}c4.o", drv, "-o", c4_bin], 120)
    return {"c0direct": str(c0_bin), "c3b": str(c3b_bin), "c4": str(c4_bin)}


def build_all(tmp, mod, c1_bin, skip_lake):
    drv = tmp / "bench_main.o"
    sh(["clang", "-std=c99", "-O3", f"-I{ROOT/'test/kissat'}", "-c", ROOT / "bench/kissat/bench_main.c", "-o", drv], 120)
    bins = build_solver_bins(tmp, mod, drv, skip_lake)
    return {"c1": str(c1_bin), **bins}


def build_extensions(tmp, fid_mod, opt_mod, c1_bin, skip_lake):
    drv = tmp / "bench_main.o"
    sh(["clang", "-std=c99", "-O3", f"-I{ROOT/'test/kissat'}", "-c", ROOT / "bench/kissat/bench_main.c", "-o", drv], 120)
    fid_bins = build_solver_bins(tmp, fid_mod, drv, skip_lake, tag_prefix="fid")
    opt_bins = build_solver_bins(tmp, opt_mod, drv, skip_lake, tag_prefix="opt")
    return {
        "c1": str(c1_bin),
        "c0_fid": fid_bins["c0direct"],
        "c4_fid": fid_bins["c4"],
        "c0_opt": opt_bins["c0direct"],
        "c4_opt": opt_bins["c4"],
    }

def run_one(eng, bin_path, cnf, timeout_s, work_mb, fuel):
    cmd = ["timeout", "-k", "2s", f"{timeout_s:.1f}s", bin_path]
    cmd += [cnf] if eng == "c1" else [str(work_mb * 1024 * 1024), str(fuel), cnf]
    t0 = time.perf_counter()
    r = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    ms = (time.perf_counter() - t0) * 1000.0
    if r.returncode in (124, 137):
        return -1, timeout_s * 1000.0
    if eng == "c1":
        st = 10 if (r.returncode == 10 or "s SATISFIABLE" in r.stdout) else (
             20 if (r.returncode == 20 or "s UNSATISFIABLE" in r.stdout) else 0)
        if st == 10: verify_dimacs_model(cnf, r.stdout)
        return st, ms
    if r.returncode != 0:
        raise RuntimeError(f"{eng} failed (rc={r.returncode}) on {cnf}:\n{r.stdout}")
    return int(r.stdout.strip().splitlines()[-1].split("\t")[1]), ms

def gm(vals, floor_ms=20.0):
    return math.exp(sum(math.log(max(v, floor_ms)) for v in vals) / len(vals)) if vals else float("nan")

def main():
    ap = argparse.ArgumentParser(description="Minimal auditable 4-way Kissat benchmark.")
    ap.add_argument("cnfs", nargs="*", help="Positional .cnf files")
    ap.add_argument("--cnf-dir", help="Directory of .cnf files")
    ap.add_argument("--manifest", help="Stage-1 JSON manifest (benchmarks[].cnf_path)")
    ap.add_argument(
        "--module", default=None,
        help="Solver module (default: KissatFidelity if present, else FullM7Fidelity; "
             "supports KissatFidelity, KissatM8Opt, Plain, FullM7Fidelity, FullM7Plus, FullM6, FullM5)",
    )
    ap.add_argument("--allow-solver-extensions", action="store_true",
                    help="Acknowledge benchmarking a non-fidelity solver extension (e.g. KissatM8Opt)")
    ap.add_argument("--extensions", action="store_true",
                    help="Run 5-way solver-extension comparison: C1 vs C0-direct/C4(KissatFidelity) vs C0-direct/C4(KissatM8Opt)")
    ap.add_argument("--fid-module", default="KissatFidelity", help="Fidelity baseline module for --extensions (default: KissatFidelity)")
    ap.add_argument("--opt-module", default="KissatM8Opt", help="Solver-extension module for --extensions (default: KissatM8Opt)")
    ap.add_argument("--c1", default=os.environ.get("KISSAT_C1_BIN") or shutil.which("kissat") or "kissat")
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--work-mb", type=int, default=64)
    ap.add_argument("--fuel", type=int, default=2000000000)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--skip-lake-build", action="store_true")
    args = ap.parse_args()
    mod = resolve_module(args.module) if args.module else default_module()
    ext_guardrail = (not args.extensions) and is_solver_extension(mod) and (not args.allow_solver_extensions)
    if ext_guardrail:
        print(
            f"[NON-FIDELITY SOLVER EXTENSION]\n"
            f"[WARNING] {mod} includes beyond-upstream solver heuristics; ratios vs C1 conflate "
            f"solver algorithm and compiler codegen! Use --module KissatFidelity for compiler benchmarks.",
            file=sys.stderr, flush=True,
        )
    items = [(p, args.work_mb) for p in args.cnfs]
    if args.cnf_dir:
        items += [(str(p), args.work_mb) for p in sorted(pathlib.Path(args.cnf_dir).glob("*.cnf"))]
    if args.manifest:
        man = json.loads(pathlib.Path(args.manifest).read_text())
        items += [(e["cnf_path"], max(args.work_mb, int(e.get("min_work_mb", 0)))) for e in man["benchmarks"]]
    if args.limit is not None: items = items[:args.limit]
    if not items: raise SystemExit("ERROR: pass .cnf files, --cnf-dir, or --manifest")
    c1 = shutil.which(args.c1) or args.c1
    if not (os.path.isfile(c1) and os.access(c1, os.X_OK)):
        raise SystemExit(f"ERROR: C1 kissat binary not executable: {args.c1}")

    if args.extensions:
        fid_mod = resolve_module(args.fid_module)
        opt_mod = resolve_module(args.opt_module)
        engines = EXT_ENGINES
        with tempfile.TemporaryDirectory(prefix="kissat-5way-ext-") as td:
            bins = build_extensions(pathlib.Path(td), fid_mod, opt_mod, c1, args.skip_lake_build)
            sizes = {e: text_bytes(bins[e]) for e in engines}
            rows = []
            print(f"\n=== [NON-FIDELITY SOLVER EXTENSION] 5-Way Extension Run ({fid_mod} vs {opt_mod}, N={len(items)}, timeout={args.timeout:.1f}s) ===", flush=True)
            for i, (cnf, wmb) in enumerate(items):
                n_eng = len(engines)
                row = {engines[(i + j) % n_eng]: run_one(engines[(i + j) % n_eng], bins[engines[(i + j) % n_eng]],
                       cnf, args.timeout, wmb, args.fuel) for j in range(n_eng)}
                assert len({st for st, _ in row.values() if st in (10, 20)}) <= 1, f"DISAGREEMENT on {cnf}: {row}"
                rows.append(row)
                tag = lambda st: {10: "S", 20: "U", -1: "TO"}.get(st, "?")
                print(f"[{i+1:3d}/{len(items)}] {pathlib.Path(cnf).name[:30]:30s} | " +
                      "  ".join(f"{e}:{tag(row[e][0]):2s} {row[e][1]:7.1f}ms" for e in engines), flush=True)

        common = [r for r in rows if all(r[e][0] in (10, 20) for e in engines)]
        print(f"\n=== [NON-FIDELITY SOLVER EXTENSION] 5-Way Summary ({fid_mod} vs {opt_mod}, N={len(rows)}, 5-way common={len(common)}, GM floor=20ms) ===")
        print(f"{'Engine':10s} {'Solved':>8s} {'TO':>4s} {'Common AM':>11s} {'Common GM':>11s} {'All-N PAR-2':>12s} {'size .text':>12s}")
        for e in engines:
            sol = sum(r[e][0] in (10, 20) for r in rows)
            tos = sum(r[e][0] == -1 for r in rows)
            cam = sum(r[e][1] for r in common) / len(common) if common else float("nan")
            cgm = gm([r[e][1] for r in common])
            par2 = sum((2 * args.timeout if r[e][0] not in (10, 20) else r[e][1] / 1000.0) for r in rows) / len(rows)
            print(f"{e:10s} {f'{sol}/{len(rows)}':>8s} {tos:4d} {cam:9.1f}ms {cgm:9.1f}ms {par2:10.3f}s {sizes[e]:10,d} B")

        def show_pairs(title, pairs):
            print(f"\n{title}")
            for label, a, b in pairs:
                mut = [r for r in rows if r[a][0] in (10, 20) and r[b][0] in (10, 20)]
                ratio = gm([r[a][1] for r in mut]) / gm([r[b][1] for r in mut]) if mut else float("nan")
                print(f"  {label:32s} ({a} / {b}) = {ratio:.4f}x  (n={len(mut)})")

        show_pairs("Compiler overhead (on Fidelity) — Wall GM (20ms floor):", [
            (f"C4({fid_mod}) / C0-direct({fid_mod})", "c4_fid", "c0_fid"),
            (f"C4({fid_mod}) / C1", "c4_fid", "c1"),
        ])
        show_pairs("Compiler overhead (on Opt) — Wall GM (20ms floor):", [
            (f"C4({opt_mod}) / C0-direct({opt_mod})", "c4_opt", "c0_opt"),
        ])
        show_pairs("Pure solver-extension gain — Wall GM (20ms floor):", [
            (f"C0-direct({opt_mod}) / C0-direct({fid_mod})", "c0_opt", "c0_fid"),
            (f"C4({opt_mod}) / C4({fid_mod})", "c4_opt", "c4_fid"),
        ])
        show_pairs("End-to-end vs upstream — Wall GM (20ms floor):", [
            (f"C4({opt_mod}) / C1", "c4_opt", "c1"),
        ])
        return

    with tempfile.TemporaryDirectory(prefix="kissat-4way-min-") as td:
        bins = build_all(pathlib.Path(td), mod, c1, args.skip_lake_build)
        sizes = {e: text_bytes(bins[e]) for e in ENGINES}
        rows = []
        print(f"\n=== Running {len(items)} CNFs sequentially (rotated order, timeout={args.timeout:.1f}s) ===", flush=True)
        for i, (cnf, wmb) in enumerate(items):
            row = {ENGINES[(i + j) % 4]: run_one(ENGINES[(i + j) % 4], bins[ENGINES[(i + j) % 4]],
                   cnf, args.timeout, wmb, args.fuel) for j in range(4)}
            assert len({st for st, _ in row.values() if st in (10, 20)}) <= 1, f"DISAGREEMENT on {cnf}: {row}"
            rows.append(row)
            tag = lambda st: {10: "S", 20: "U", -1: "TO"}.get(st, "?")
            print(f"[{i+1:3d}/{len(items)}] {pathlib.Path(cnf).name[:34]:34s} | " +
                  "  ".join(f"{e}:{tag(row[e][0]):2s} {row[e][1]:7.1f}ms" for e in ENGINES), flush=True)

    common = [r for r in rows if all(r[e][0] in (10, 20) for e in ENGINES)]
    hdr_prefix = "[NON-FIDELITY SOLVER EXTENSION] " if ext_guardrail else ""
    print(f"\n=== {hdr_prefix}Summary ({mod}, N={len(rows)}, 4-way common={len(common)}, GM floor=20ms) ===")
    print(f"{'Engine':10s} {'Solved':>8s} {'TO':>4s} {'Common AM':>11s} {'Common GM':>11s} {'All-N PAR-2':>12s} {'size .text':>12s}")
    for e in ENGINES:
        sol = sum(r[e][0] in (10, 20) for r in rows)
        tos = sum(r[e][0] == -1 for r in rows)
        cam = sum(r[e][1] for r in common) / len(common) if common else float("nan")
        cgm = gm([r[e][1] for r in common])
        par2 = sum((2 * args.timeout if r[e][0] not in (10, 20) else r[e][1] / 1000.0) for r in rows) / len(rows)
        print(f"{e:10s} {f'{sol}/{len(rows)}':>8s} {tos:4d} {cam:9.1f}ms {cgm:9.1f}ms {par2:10.3f}s {sizes[e]:10,d} B")
    print("\nPairwise mutually-solved Wall GM ratios (20ms floor):")
    for a, b in (("c4", "c0direct"), ("c4", "c3b"), ("c4", "c1"), ("c0direct", "c1")):
        mut = [r for r in rows if r[a][0] in (10, 20) and r[b][0] in (10, 20)]
        ratio = gm([r[a][1] for r in mut]) / gm([r[b][1] for r in mut]) if mut else float("nan")
        print(f"  {a:8s} / {b:8s} = {ratio:.4f}x  (n={len(mut)})")

if __name__ == "__main__":
    main()
