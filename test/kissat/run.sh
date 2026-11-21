#!/usr/bin/env bash
# Differential verification suite for X1 Stage A (LeanQbe.T.Examples.Kissat):
# Compares across:
#   1. X2-LayerA pure-Lean cdclSolve (verified during artifact generation)
#   2. PrintCpp + g++ -std=c++20 -O2 -DTQBE_CATCH_UB (aligned + unaligned work_ptr)
#   3. PrintCpp + clang++ -std=c++20 -O2 -fsanitize=undefined,address -DTQBE_CATCH_UB
#   4. Native x64 assembly (x64Target) + mmap guard pages + DIMACS model verifier
#   5. Native Arm64 assembly (armTarget) via qemu-aarch64 + mmap guard pages + model verifier
#   6. Stock QBE (amd64_sysv + arm64 via qemu-aarch64) when stock QBE source/binary exists
#   7. Reference kissat CLI (--basic --lucky=0) when kissat exists in PATH or scratch/
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-kissat.XXXXXX")}"
cleanup() {
  if [ -z "$OUT_USER" ]; then
    rm -rf "$OUT"
  fi
}
trap cleanup EXIT
echo "outputs in $OUT"

echo "== 1. build Kissat Solver/Test and generate C++20 / QBE / corpus artifacts =="
timeout 600 lake build --wfail LeanQbe.T.Examples.Kissat.Solver LeanQbe.T.Driver \
  LeanQbe.T.Amd64.Targ LeanQbe.T.Arm64.Targ LeanQbeTest.T.KissatC0Test
timeout 120 lake env lean --run LeanQbeTest/T/KissatC0Test.lean "$OUT"

RT_INC="$ROOT/LeanQbe/T/Runtime"
KTEST_INC="$ROOT/test/kissat"
COMMON_CXX="-std=c++20 -O2 -Wall -Wextra -Werror -I$RT_INC -I$KTEST_INC -I$OUT"
COMMON_C="-O1 -Wall -Wextra -Werror -I$KTEST_INC -I$OUT"

echo "== 2. g++ -std=c++20 -DTQBE_CATCH_UB (PrintCpp differential) =="
timeout 60 g++ $COMMON_CXX -DTQBE_CATCH_UB "$OUT/kissat_driver.cpp" -o "$OUT/kissat_gpp"
timeout 60 "$OUT/kissat_gpp"

echo "== 3. clang++ -std=c++20 -fsanitize=undefined,address -DTQBE_CATCH_UB =="
timeout 60 clang++ $COMMON_CXX -fsanitize=undefined,address -DTQBE_CATCH_UB \
  "$OUT/kissat_driver.cpp" -o "$OUT/kissat_asan"
timeout 60 "$OUT/kissat_asan"

echo "== 4. native x64 codegen (x64Target + gcc + mmap guard pages) =="
timeout 120 lake env lean --run test/kissat/emit_x64.lean "$OUT/kissat_x64.s"
timeout 60 gcc $COMMON_C -no-pie test/kissat/kissat_main.c "$OUT/kissat_x64.s" \
  -o "$OUT/kissat_x64"
timeout 60 "$OUT/kissat_x64" > "$OUT/x64.out"
tail -n 1 "$OUT/x64.out"

echo "== 5. native Arm64 codegen (armTarget + aarch64-linux-gnu-gcc + qemu-aarch64) =="
timeout 120 lake env lean --run test/kissat/emit_arm64.lean "$OUT/kissat_arm64.s"
timeout 60 aarch64-linux-gnu-gcc $COMMON_C test/kissat/kissat_main.c "$OUT/kissat_arm64.s" \
  -o "$OUT/kissat_arm64" 2>"$OUT/arm64_cc.log" || { cat "$OUT/arm64_cc.log" >&2; exit 1; }
grep -v -e 'SFrame' "$OUT/arm64_cc.log" >&2 || true
timeout 60 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/kissat_arm64" > "$OUT/arm64.out"
diff -u "$OUT/x64.out" "$OUT/arm64.out"

QBE_SRC="${QBE_SRC:-$ROOT/qbe}"
if [ -z "${QBE:-}" ] && [ ! -d "$QBE_SRC" ]; then
  QBE="$(command -v qbe || true)"
fi
if [ -n "${QBE:-}" ] || [ -d "$QBE_SRC" ]; then
  echo "== 6. stock QBE cross-check (amd64_sysv + arm64) =="
  if [ -z "${QBE:-}" ]; then
    cp -r "$QBE_SRC" "$OUT/qbe-src"
    timeout 120 make -C "$OUT/qbe-src" clean >/dev/null 2>&1 || true
    timeout 120 make -C "$OUT/qbe-src" -j"$(nproc)" >"$OUT/qbe-build.log" 2>&1
    QBE="$OUT/qbe-src/qbe"
  fi
  timeout 60 "$QBE" -t amd64_sysv -o "$OUT/kissat_qbe_x64.s" "$OUT/kissat.ssa"
  timeout 60 gcc $COMMON_C -no-pie test/kissat/kissat_main.c "$OUT/kissat_qbe_x64.s" \
    -o "$OUT/kissat_qbe_x64"
  timeout 60 "$OUT/kissat_qbe_x64" > "$OUT/qbe_x64.out"
  diff -u "$OUT/x64.out" "$OUT/qbe_x64.out"

  timeout 60 "$QBE" -t arm64 -o "$OUT/kissat_qbe_arm64.s" "$OUT/kissat.ssa"
  timeout 60 aarch64-linux-gnu-gcc $COMMON_C test/kissat/kissat_main.c \
    "$OUT/kissat_qbe_arm64.s" -o "$OUT/kissat_qbe_arm64" \
    2>"$OUT/qbe_arm64_cc.log" || { cat "$OUT/qbe_arm64_cc.log" >&2; exit 1; }
  grep -v -e 'SFrame' "$OUT/qbe_arm64_cc.log" >&2 || true
  timeout 60 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/kissat_qbe_arm64" \
    > "$OUT/qbe_arm64.out"
  diff -u "$OUT/x64.out" "$OUT/qbe_arm64.out"
else
  echo "NOTE: stock QBE not found (set QBE, QBE_SRC, or place checkout at $ROOT/qbe); skipping step 6."
fi

KISSAT_BIN="${KISSAT_BIN:-$(command -v kissat || true)}"
if [ -z "$KISSAT_BIN" ] && [ -x "$ROOT/scratch/kissat" ]; then
  KISSAT_BIN="$ROOT/scratch/kissat"
fi
if [ -n "$KISSAT_BIN" ]; then
  echo "== 7. reference kissat CLI cross-check ($KISSAT_BIN --basic --lucky=0) =="
  timeout 120 python3 - "$KISSAT_BIN" "$OUT/kissat_cases.h" "$OUT" <<'PY'
import re, subprocess, sys
kbin, hdr, out = sys.argv[1], sys.argv[2], sys.argv[3]
src = open(hdr).read()
pat = r'\{"([^"]+)",\s*"((?:[^"\\]|\\.)*)",\s*\d+ULL,\s*\d+ULL,\s*\d+ULL,\s*(\d+)ULL\}'
for m in re.finditer(pat, src):
    nm, cnf_esc, exp = m.group(1), m.group(2), int(m.group(3))
    if exp not in (10, 20) or nm.startswith(("fuel_", "tiny_", "bad_")):
        continue
    cnf = bytes(cnf_esc, "utf-8").decode("unicode_escape").encode("latin1")
    p = f"{out}/{nm}.cnf"
    open(p, "wb").write(cnf)
    r = subprocess.run(
        ["timeout", "30", kbin, "--basic", "--lucky=0", "-q", p], capture_output=True)
    if r.returncode != exp:
        raise SystemExit(f"kissat mismatch on {nm}: got {r.returncode}, exp {exp}")
print("PASS: reference kissat cross-check")
PY
fi

echo "== 8. FullM3 unified differential check (PrintCpp ASan/UBSan + Native x64 + Arm64) =="
timeout 600 lake build --wfail LeanQbe.T.Examples.Kissat.FullM3 LeanQbe.T.PrintCpp \
  LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Arm64.Targ \
  Kraken.X64.PrintATT Kraken.AArch64.Print
timeout 180 lake env lean --run test/kissat/emit_m3_x64.lean "$OUT/m3_x64.s" "$OUT/m3_gen.hpp"
timeout 180 lake env lean --run test/kissat/emit_m3_arm64.lean "$OUT/m3_arm64.s"

cat > "$OUT/m3_bridge.cpp" <<'CPP'
#include <cstdint>
#include "tqbe_rt.hpp"

namespace tqbe_gen {
#include "m3_gen.hpp"
}

extern "C" uint64_t kissat_solve_bytes(
    const uint8_t *cnf_ptr, uint64_t cnf_len,
    uint8_t *work_ptr, uint64_t work_len, uint64_t fuel) {
  ::tqbe::Mem mem;
  return tqbe_gen::kissat_solve_bytes(
      mem,
      ::tqbe::bits<64>(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(cnf_ptr))),
      ::tqbe::bits<64>(cnf_len),
      ::tqbe::bits<64>(static_cast<uint64_t>(reinterpret_cast<uintptr_t>(work_ptr))),
      ::tqbe::bits<64>(work_len),
      ::tqbe::bits<64>(fuel)).word(0);
}
CPP

timeout 60 gcc -std=c99 -O2 -Wall -Wextra -Werror -I"$KTEST_INC" \
  -c bench/kissat/bench_main.c -o "$OUT/m3_main.o"
timeout 240 clang++ -std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=undefined,address \
  -DTQBE_NATIVE_MEM -I"$RT_INC" -I"$OUT" "$OUT/m3_bridge.cpp" "$OUT/m3_main.o" -o "$OUT/m3_asan"
timeout 60 gcc -std=c99 -O2 -Wall -Wextra -Werror -no-pie -I"$KTEST_INC" \
  bench/kissat/bench_main.c "$OUT/m3_x64.s" -o "$OUT/m3_x64"
timeout 60 aarch64-linux-gnu-gcc -std=c99 -O2 -Wall -Wextra -Werror -I"$KTEST_INC" \
  bench/kissat/bench_main.c "$OUT/m3_arm64.s" -o "$OUT/m3_arm64" 2>"$OUT/m3_arm64_cc.log" || {
    cat "$OUT/m3_arm64_cc.log" >&2; exit 1; }
grep -v -e 'SFrame' "$OUT/m3_arm64_cc.log" >&2 || true

mkdir -p "$OUT/m3_cnfs"
timeout 60 python3 -B bench/kissat/gen_canary_cnfs.py "$OUT/m3_cnfs" >/dev/null
timeout 240 python3 -B - "$OUT" <<'PY'
import glob, os, subprocess, sys

out = sys.argv[1]
cdir = os.path.join(out, "m3_cnfs")
cases = [
    ("edge_empty.cnf", "", 64, 1000, 0),
    ("edge_bad_hdr.cnf", "p sat 1 1\n", 65536, 1000, 0),
    ("edge_bad_lit.cnf", "p cnf 1 1\n2 0\n", 65536, 1000, 0),
    ("tiny_work.cnf", "p cnf 1 1\n1 0\n", 64, 1000, 0),
    ("sat_unit.cnf", "p cnf 1 1\n1 0\n", 1 << 20, 10000, 10),
    ("unsat_unit.cnf", "p cnf 1 2\n1 0\n-1 0\n", 1 << 20, 10000, 20),
    ("sat_chain.cnf",
     "p cnf 4 4\n-1 2 0\n-2 3 0\n-3 4 0\n1 2 3 4 0\n", 1 << 20, 10000, 10),
    ("unsat_php3.cnf",
     "p cnf 6 9\n1 2 0\n3 4 0\n5 6 0\n-1 -3 0\n-1 -5 0\n-3 -5 0\n-2 -4 0\n-2 -6 0\n-4 -6 0\n",
     1 << 20, 50000, 20),
]

def run_tel(cmd):
    r = subprocess.run(cmd, capture_output=True, text=True, check=True)
    toks = r.stdout.strip().split("\t")
    kv = dict(t.split("=", 1) for t in toks[3:] if "=" in t)
    return (int(toks[1]), kv.get("conflicts"), kv.get("learned_lits"),
            kv.get("min_removed"), kv.get("search_ticks"))

def check_all(path, work, fuel, exp=None, allow_unk=False):
    args = ["--full-telemetry-m2", str(work), str(fuel), path]
    t_asan = run_tel(["timeout", "20", f"{out}/m3_asan"] + args)
    t_x64 = run_tel(["timeout", "20", f"{out}/m3_x64"] + args)
    t_arm = run_tel(["timeout", "20", "qemu-aarch64", "-L", "/usr/aarch64-linux-gnu",
                     f"{out}/m3_arm64"] + args)
    if not (t_asan == t_x64 == t_arm):
        raise SystemExit(f"M3 parity mismatch on {path}: asan={t_asan} x64={t_x64} arm={t_arm}")
    st = t_x64[0]
    if exp is not None and not (allow_unk and st == 0) and st != exp:
        raise SystemExit(f"M3 status mismatch on {path}: got={st}, exp={exp}")

for name, txt, work, fuel, exp in cases:
    p = os.path.join(cdir, name)
    open(p, "w").write(txt)
    check_all(p, work, fuel, exp=exp)

for p in sorted(glob.glob(os.path.join(cdir, "c*.cnf"))):
    base = os.path.basename(p)
    if any(k in base for k in ("_small", "6_5", "500", "256", "c02_", "c03_", "c04_", "c05_", "c06_", "c07_")):
        check_all(p, 8 << 20, 300000, exp=20, allow_unk=True)
print("PASS: FullM3 3-way differential verification (PrintCpp ASan/UBSan == x64 == Arm64)")
PY

echo "== test/kissat/run.sh: ALL DIFFERENTIAL CHECKS PASSED =="
