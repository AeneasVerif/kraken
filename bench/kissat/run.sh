#!/usr/bin/env bash
# Stage 2 (D-Core+) Differential Verification & Multi-Family DIMACS Benchmark Suite.
# Compares:
#   1. CorePlus PrintCpp (g++ -std=c++20 -O2 -DTQBE_CATCH_UB + clang++ ASan/UBSan) on 54 corpus cases
#   2. CorePlus native x64 (x64Target) + native Arm64 (armTarget via qemu-aarch64) with mmap guard pages
#   3. Benchmark suite (gen_cnfs.py + stock kissat test/cnf/*.cnf):
#      D-Min (x64) vs CorePlus (x64 & arm64) vs stock kissat (--basic --lucky=0, --plain, default)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-kissat-bench.XXXXXX")}"
cleanup() {
  if [ -z "$OUT_USER" ]; then
    rm -rf "$OUT"
  fi
}
trap cleanup EXIT
echo "outputs in $OUT"

KISSAT_SRC="${KISSAT_SRC:-}"
if [ -z "$KISSAT_SRC" ] && [ -d "$ROOT/scratch/kissat" ]; then
  KISSAT_SRC="$ROOT/scratch/kissat"
fi
WORK_BYTES="${WORK_BYTES:-8388608}"
FUEL="${FUEL:-400000}"

echo "== 1. build CorePlus, Solver, Codegen Drivers, and KissatCorePlusC0Test =="
timeout 600 lake build --wfail \
  LeanQbe.T.Examples.Kissat.CorePlus LeanQbe.T.Examples.Kissat.Solver \
  LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Arm64.Targ \
  LeanQbeTest.T.KissatCorePlusC0Test

mkdir -p "$OUT/coreplus_hdr" "$OUT/cnfs/gen" "$OUT/cnfs/kissat_test"
timeout 120 lake env lean --run LeanQbeTest/T/KissatCorePlusC0Test.lean "$OUT"
printf '#include "../coreplus_cases.h"\n' > "$OUT/coreplus_hdr/kissat_cases.h"

RT_INC="$ROOT/LeanQbe/T/Runtime"
KTEST_INC="$ROOT/test/kissat"
COMMON_CXX="-std=c++20 -O2 -Wall -Wextra -Werror -I$RT_INC -I$KTEST_INC -I$OUT"
COMMON_C="-O2 -Wall -Wextra -Werror -I$KTEST_INC -I$OUT"

echo "== 2. CorePlus PrintCpp (g++ + clang++ ASan/UBSan) differential corpus =="
timeout 60 g++ $COMMON_CXX -DTQBE_CATCH_UB "$OUT/coreplus_driver.cpp" -o "$OUT/coreplus_gpp"
timeout 60 "$OUT/coreplus_gpp"
timeout 60 clang++ $COMMON_CXX -fsanitize=undefined,address -DTQBE_CATCH_UB \
  "$OUT/coreplus_driver.cpp" -o "$OUT/coreplus_asan"
timeout 60 "$OUT/coreplus_asan"

echo "== 3. CorePlus native x64 + Arm64 guarded corpus + D-Min x64 build =="
timeout 120 lake env lean --run test/common/emit.lean --arch x64 --suite coreplus "$OUT/coreplus_x64.s"
timeout 60 gcc $COMMON_C -I"$OUT/coreplus_hdr" -no-pie test/kissat/kissat_main.c \
  "$OUT/coreplus_x64.s" -o "$OUT/coreplus_corpus_x64"
timeout 60 "$OUT/coreplus_corpus_x64" > "$OUT/corpus_x64.out"
tail -n 1 "$OUT/corpus_x64.out"

timeout 120 lake env lean --run test/common/emit.lean --arch arm64 --suite coreplus "$OUT/coreplus_arm64.s"
timeout 60 aarch64-linux-gnu-gcc $COMMON_C -I"$OUT/coreplus_hdr" test/kissat/kissat_main.c \
  "$OUT/coreplus_arm64.s" -o "$OUT/coreplus_corpus_arm64" 2>"$OUT/arm64_cc.log" || {
    cat "$OUT/arm64_cc.log" >&2; exit 1;
  }
grep -v -e 'SFrame' "$OUT/arm64_cc.log" >&2 || true
timeout 60 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/coreplus_corpus_arm64" \
  > "$OUT/corpus_arm64.out"
diff -u "$OUT/corpus_x64.out" "$OUT/corpus_arm64.out"
echo "PASS: CorePlus x64 == Arm64 guarded corpus differential"

timeout 120 lake env lean --run test/common/emit.lean --arch x64 --suite kissat "$OUT/dmin_x64.s"
timeout 60 gcc $COMMON_C -no-pie bench/kissat/bench_main.c "$OUT/dmin_x64.s" \
  -o "$OUT/bench_dmin_x64"
timeout 60 gcc $COMMON_C -no-pie bench/kissat/bench_main.c "$OUT/coreplus_x64.s" \
  -o "$OUT/bench_coreplus_x64"
timeout 60 aarch64-linux-gnu-gcc $COMMON_C bench/kissat/bench_main.c "$OUT/coreplus_arm64.s" \
  -o "$OUT/bench_coreplus_arm64" 2>"$OUT/bench_arm64_cc.log" || {
    cat "$OUT/bench_arm64_cc.log" >&2; exit 1;
  }
grep -v -e 'SFrame' "$OUT/bench_arm64_cc.log" >&2 || true

echo "== 4. Build stock Kissat 4.0.4 (with options enabled, without -DNOPTIONS) =="
if [ -z "${KISSAT_BIN:-}" ]; then
  if [ -n "$KISSAT_SRC" ] && [ -d "$KISSAT_SRC" ]; then
    cp -a "$KISSAT_SRC" "$OUT/kissat-src"
    (
      cd "$OUT/kissat-src"
      rm -rf build makefile
      timeout 60 ./configure >/dev/null
      timeout 180 make -j"$(nproc)" >/dev/null
    )
    KISSAT_BIN="$OUT/kissat-ref"
    cp "$OUT/kissat-src/build/kissat" "$KISSAT_BIN"
  else
    KISSAT_BIN="$(command -v kissat || true)"
  fi
fi
if [ -n "${KISSAT_BIN:-}" ]; then
  # Verify options work (NOT built with -DNOPTIONS)
  rc=0
  printf 'p cnf 0 0\n' | timeout 10 "$KISSAT_BIN" --basic --lucky=0 -q >/dev/null 2>&1 || rc=$?
  if [ "$rc" -eq 10 ]; then
    echo "Using stock kissat: $KISSAT_BIN"
  else
    echo "NOTE: kissat binary '$KISSAT_BIN' unavailable or lacks --basic/--lucky=0; skipping stock-kissat comparison rows."
    KISSAT_BIN=""
  fi
else
  KISSAT_BIN=""
  echo "NOTE: no stock kissat binary or KISSAT_SRC found (set KISSAT_BIN or KISSAT_SRC); skipping stock-kissat comparison rows."
fi

echo "== 5. Generate multi-family DIMACS CNFs + collect stock kissat test/cnf =="
timeout 60 python3 bench/kissat/gen_cnfs.py "$OUT/cnfs/gen"
if [ -n "$KISSAT_SRC" ] && [ -d "$KISSAT_SRC/test/cnf" ]; then
  for f in "$KISSAT_SRC/test/cnf"/*.cnf; do
    [ -f "$f" ] && [ ! -L "$f" ] || continue
    cp "$f" "$OUT/cnfs/kissat_test/"
  done
fi

echo "== 6. Run differential benchmark comparison & telemetry =="
timeout 300 python3 - "$OUT" "$WORK_BYTES" "$FUEL" \
  "$OUT/bench_dmin_x64" "$OUT/bench_coreplus_x64" "$OUT/bench_coreplus_arm64" \
  "$KISSAT_BIN" <<'PY'
import glob, os, statistics, subprocess, sys, time

out, work_bytes, fuel, dmin_bin, cp_x64_bin, cp_arm_bin, kissat_bin = sys.argv[1:8]
gen_cnfs = sorted(glob.glob(os.path.join(out, "cnfs/gen/*.cnf")))
ktest_cnfs = sorted(glob.glob(os.path.join(out, "cnfs/kissat_test/*.cnf")))
all_cnfs = [(p, "gen/" + os.path.basename(p)) for p in gen_cnfs] + [
    (p, "ktest/" + os.path.basename(p)) for p in ktest_cnfs
]
assert len(all_cnfs) > 0, "no benchmark CNFs found"

def parse_bench_lines(stdout_text):
    res = {}
    for line in stdout_text.strip().splitlines():
        parts = line.split("\t")
        if len(parts) != 6:
            raise RuntimeError(f"bad bench line: {line!r}")
        p, st, ms, conf, lrn, mrem = parts
        res[p] = (int(st), float(ms), int(conf), int(lrn), int(mrem))
    return res

def run_native_batch(cmd_prefix, paths, telemetry=False):
    args = list(cmd_prefix) + (["--telemetry"] if telemetry else []) + [work_bytes, fuel] + paths
    proc = subprocess.run(args, capture_output=True, text=True, timeout=180)
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr)
        raise SystemExit(f"solver failed ({proc.returncode}): {' '.join(cmd_prefix)}")
    return parse_bench_lines(proc.stdout)

paths = [p for p, _ in all_cnfs]
print(f"Benchmark corpus: {len(gen_cnfs)} generated + {len(ktest_cnfs)} stock-test = {len(paths)} CNFs (work={int(work_bytes)//1048576}MiB, fuel={fuel})")

dmin_res = run_native_batch([dmin_bin], paths, telemetry=False)
cp_x64_res = run_native_batch([cp_x64_bin], paths, telemetry=True)
cp_arm_res = run_native_batch(
    ["qemu-aarch64", "-L", "/usr/aarch64-linux-gnu", cp_arm_bin], paths, telemetry=True
)

def run_kissat_mode(flags, cnf_paths):
    out_map = {}
    for p in cnf_paths:
        t0 = time.monotonic()
        r = subprocess.run(["timeout", "3", kissat_bin] + flags + ["-q", p], capture_output=True)
        ms = (time.monotonic() - t0) * 1000.0
        st = r.returncode if r.returncode in (10, 20) else 0
        out_map[p] = (st, ms, 0, 0, 0)
    return out_map

solvers = [
    ("D-Min (x64)", dmin_res),
    ("CorePlus (x64)", cp_x64_res),
    ("CorePlus (Arm64 qemu)", cp_arm_res),
]
k_def = None
if kissat_bin:
    k_basic = run_kissat_mode(["--basic", "--lucky=0"], paths)
    k_plain = run_kissat_mode(["--plain"], paths)
    k_def = run_kissat_mode([], paths)
    solvers.extend([
        ("kissat --basic --lucky=0", k_basic),
        ("kissat --plain", k_plain),
        ("kissat (default)", k_def),
    ])

# Verify 0 SAT/UNSAT disagreements across all active solver configurations + x64 vs Arm64 parity
disagree = 0
for p, label in all_cnfs:
    if cp_x64_res[p][0] != cp_arm_res[p][0]:
        print(f"ARM64 PARITY MISMATCH {label}: x64={cp_x64_res[p][0]} arm64={cp_arm_res[p][0]}", file=sys.stderr)
        disagree += 1
    verdicts = {name: tbl[p][0] for name, tbl in solvers if tbl[p][0] in (10, 20)}
    uniq = set(verdicts.values())
    if len(uniq) > 1:
        print(f"DISAGREEMENT {label}: {verdicts}", file=sys.stderr)
        disagree += 1
assert disagree == 0, f"Found {disagree} disagreements!"

print("\n== Overall Solver Comparison ==")
hdr = f"{'Solver':<26} {'Solved':>9} {'SAT':>5} {'UNSAT':>5} {'Avg(ms)':>9} {'Max(ms)':>9}  Notes / Telemetry"
print(hdr)
print("-" * len(hdr) + "-----------------------------")
tot = len(paths)
for name, tbl in solvers:
    solved = [v for v in tbl.values() if v[0] in (10, 20)]
    nsat = sum(1 for v in solved if v[0] == 10)
    nunsat = sum(1 for v in solved if v[0] == 20)
    ms_list = [v[1] for v in tbl.values()]
    avg_ms = statistics.mean(ms_list)
    max_ms = max(ms_list)
    note = ""
    if "CorePlus" in name:
        confs = sum(tbl[p][2] for p in paths)
        lrn = sum(tbl[p][3] for p in paths)
        mrem = sum(tbl[p][4] for p in paths)
        pct = (100.0 * mrem / (lrn + mrem)) if (lrn + mrem) > 0 else 0.0
        note = f"confl={confs} lrn={lrn} min_rem={mrem} ({pct:.1f}% stripped)"
    print(f"{name:<26} {len(solved):>4}/{tot:<4} {nsat:>5} {nunsat:>5} {avg_ms:>9.2f} {max_ms:>9.2f}  {note}")

# Per-family breakdown on generated suite (D-Min vs CorePlus vs optional kissat default)
families = [
    ("php", lambda l: l.startswith("gen/php_")),
    ("tseitin", lambda l: l.startswith("gen/tseitin_")),
    ("ordering", lambda l: l.startswith("gen/ordering_")),
    ("pebbling", lambda l: l.startswith("gen/pebbling_")),
    ("r3sat", lambda l: l.startswith("gen/r3sat_")),
    ("kissat_test", lambda l: l.startswith("ktest/")),
]
print("\n== Per-Family Solved Breakdown & CorePlus Minimization Impact ==")
print(f"{'Family':<14} {'N':>4} {'D-Min':>7} {'Core+':>7} {'Kissat':>7} {'CP-confl':>10} {'CP-lrn':>9} {'MinRem(%)':>12}")
for fam, pred in families:
    sub = [p for p, l in all_cnfs if pred(l)]
    if not sub:
        continue
    n = len(sub)
    sd = sum(1 for p in sub if dmin_res[p][0] in (10, 20))
    sc = sum(1 for p in sub if cp_x64_res[p][0] in (10, 20))
    sk = str(sum(1 for p in sub if k_def[p][0] in (10, 20))) if k_def is not None else "n/a"
    confs = sum(cp_x64_res[p][2] for p in sub)
    lrn = sum(cp_x64_res[p][3] for p in sub)
    mrem = sum(cp_x64_res[p][4] for p in sub)
    pct = (100.0 * mrem / (lrn + mrem)) if (lrn + mrem) > 0 else 0.0
    print(f"{fam:<14} {n:>4} {sd:>7} {sc:>7} {sk:>7} {confs:>10} {lrn:>9} {mrem:>6} ({pct:>4.1f}%)")

print(f"\nPASS: 0 SAT/UNSAT disagreements across all {len(solvers)} solver configurations.")
PY

echo "== bench/kissat/run.sh: ALL DIFFERENTIAL & BENCHMARK CHECKS PASSED =="
