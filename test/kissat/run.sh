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
if [ ! -d "$QBE_SRC" ] && [ -d /usr/local/google/home/andreser/lean-qbe/qbe ]; then
  QBE_SRC=/usr/local/google/home/andreser/lean-qbe/qbe
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

echo "== test/kissat/run.sh: ALL DIFFERENTIAL CHECKS PASSED =="
