#!/usr/bin/env python3
"""Minimal auditable 4-way Kissat benchmark: C1 vs C0-direct vs C3b vs C4 (x86-64)."""
import argparse, json, math, os, pathlib, shutil, subprocess, sys, tempfile, time

ROOT = pathlib.Path(__file__).resolve().parents[2]
MODS = {
    "FullM5": ("m5", "FullM5", "FullM5.m5Module", "LeanQbe.T.MainInline",
               "((FullM5.m5Module).optInlinePolicy InlinePolicy.b5).fns"),
    "FullM6": ("m6", "FullM6", "FullM6.m6Module", "LeanQbe.T.Examples.Kissat.FullM6Inl", "FullM6Inl.m6InlFns"),
    "FullM7Plus": ("m7plus", "FullM7PlusAssembly", "FullM7Plus.m7PlusModule",
                   "LeanQbe.T.Examples.Kissat.FullM7PlusInl", "FullM7PlusInl.m7PlusInlFns"),
    "FullM7Fidelity": ("m7fidelity", "FullM7FidelityAssembly", "FullM7Fidelity.m7FidelityModule",
                       "LeanQbe.T.Examples.Kissat.FullM7FidelityInl", "FullM7FidelityInl.m7FidInlFns"),
}
ENGINES = ("c1", "c0direct", "c3b", "c4")

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

def build_all(tmp, mod, c1_bin, skip_lake):
    c0_tgt, lean_file, mod_expr, extra_imp, fns_expr = MODS[mod]
    drv = tmp / "bench_main.o"
    sh(["clang", "-std=c99", "-O3", f"-I{ROOT/'test/kissat'}", "-c", ROOT / "bench/kissat/bench_main.c", "-o", drv], 120)
    if not skip_lake:
        sh(["lake", "build", "--wfail", f"LeanQbe.T.Examples.Kissat.{lean_file}", extra_imp,
            "LeanQbe.T.PrintCpp", "LeanQbe.T.Opt", "LeanQbe.T.Driver",
            "LeanQbe.T.Amd64.Targ", "LeanQbe.T.Amd64.PrintATTAlign"], 1800)
    sh([sys.executable, "-B", ROOT / "bench/kissat/extract_c0_direct.py",
        "--target", c0_tgt, "--out", tmp / "c0.c", "--check-fns", "lean"], 120)
    sh(["clang", "-std=c99", "-O3", "-fwrapv", "-fno-strict-aliasing",
        f"-I{ROOT/'LeanQbe/T/Frontend/C0'}", "-c", tmp / "c0.c", "-o", tmp / "c0.o"], 180)
    sh(["clang", tmp / "c0.o", drv, "-o", tmp / "c0direct"], 120)
    (tmp / "Emit.lean").write_text(
        f"import LeanQbe.T.Examples.Kissat.{lean_file}\nimport {extra_imp}\n"
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
    sh(["lake", "env", "lean", "--run", tmp / "Emit.lean", tmp / "gen.hpp", tmp / "c4.s"], 600)
    (tmp / "c3b.cpp").write_text(
        '#include <cstdint>\n#include "tqbe_rt.hpp"\nnamespace tqbe_gen {\n#include "gen.hpp"\n}\n'
        'extern "C" uint64_t kissat_solve_bytes(const uint8_t *c, uint64_t cl, uint8_t *w, uint64_t wl, uint64_t f) {\n'
        '  ::tqbe::Mem m; return tqbe_gen::kissat_solve_bytes(m, ::tqbe::bits<64>((uintptr_t)c), '
        '::tqbe::bits<64>(cl), ::tqbe::bits<64>((uintptr_t)w), ::tqbe::bits<64>(wl), ::tqbe::bits<64>(f)).word(0); }\n')
    sh(["clang++", "-std=c++20", "-O3", "-DTQBE_NATIVE_MEM",
        f"-I{ROOT/'LeanQbe/T/Runtime'}", f"-I{tmp}", "-c", tmp / "c3b.cpp", "-o", tmp / "c3b.o"], 300)
    sh(["clang++", tmp / "c3b.o", drv, "-o", tmp / "c3b"], 120)
    sh(["gcc", "-c", tmp / "c4.s", "-o", tmp / "c4.o"], 120)
    sh(["gcc", "-no-pie", tmp / "c4.o", drv, "-o", tmp / "c4"], 120)
    return {"c1": str(c1_bin), "c0direct": str(tmp / "c0direct"), "c3b": str(tmp / "c3b"), "c4": str(tmp / "c4")}

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
    ap.add_argument("--module", choices=list(MODS), default="FullM6")
    ap.add_argument("--c1", default=os.environ.get("KISSAT_C1_BIN") or shutil.which("kissat") or "kissat")
    ap.add_argument("--timeout", type=float, default=30.0)
    ap.add_argument("--work-mb", type=int, default=64)
    ap.add_argument("--fuel", type=int, default=2000000000)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--skip-lake-build", action="store_true")
    args = ap.parse_args()
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

    with tempfile.TemporaryDirectory(prefix="kissat-4way-min-") as td:
        bins = build_all(pathlib.Path(td), args.module, c1, args.skip_lake_build)
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
    print(f"\n=== Summary ({args.module}, N={len(rows)}, 4-way common={len(common)}, GM floor=20ms) ===")
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
