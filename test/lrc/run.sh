#!/usr/bin/env bash
# Differential verification suite for X3-R0 (`LeanQbe.T.LeanLRC`):
# Compares bit-for-bit across:
#   1. Native Lean 4 reference (`lean -c` + `leanc`)
#   2. `PrintCpp` + `g++ -std=c++20 -O2` (with `-DTQBE_CATCH_UB` trap tests)
#   3. `PrintCpp` + `clang++ -std=c++20 -O2 -fsanitize=undefined,address` (bench + scalarStruct)
#   4. Native x64 assembly (`LeanQbe.T.compile` x64Target) linked with `lrc_main.c`
#   5. Native Arm64 assembly (`LeanQbe.T.compile` armTarget) via `qemu-aarch64`
#   6. Stock QBE (`amd64_sysv` & `arm64` via `qemu-aarch64`) when stock QBE checkout exists
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-lrc.XXXXXX")}"
cleanup() {
  if [ -z "${KEEP_OUT:-}" ]; then
    rm -rf "$OUT"
  fi
}
trap cleanup EXIT
echo "outputs in $OUT"

echo "== 1. build LeanLRC modules and generate C++20 / QBE artifacts =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 300 lake build --wfail LeanQbe.T.LeanLRC.ToT LeanQbe.T.Driver LeanQbe.T.Amd64.Targ \
    LeanQbe.T.Amd64.PrintATTAlign LeanQbe.T.Arm64.Targ LeanQbeTest.T.LeanLRCTest
else
  echo "SKIP_BUILD=1: skipping lake build LeanLRC modules"
fi
timeout 120 lake env lean --run LeanQbeTest/T/LeanLRCTest.lean "$OUT"

echo "== 2. build & run native Lean 4 reference oracle (leanc) =="
timeout 60 lean -c "$OUT/ref_lean.c" test/lrc/ref_lean.lean
timeout 60 leanc -O2 "$OUT/ref_lean.c" -o "$OUT/ref_lean_bin"
timeout 30 "$OUT/ref_lean_bin" > "$OUT/ref.out"

RT_INC="$ROOT/LeanQbe/T/Runtime"
COMMON_CXX="-std=c++20 -O2 -Wall -Wextra -Werror -I$RT_INC -I$OUT"

echo "== 3. g++ -std=c++20 (catch UB + runtime exit traps) =="
timeout 60 g++ $COMMON_CXX -DTQBE_CATCH_UB "$OUT/lrc_driver.cpp" -o "$OUT/lrc_gpp"
timeout 30 "$OUT/lrc_gpp" > "$OUT/gpp.out"
diff -u "$OUT/ref.out" "$OUT/gpp.out"
timeout 60 g++ $COMMON_CXX "$OUT/lrc_scalar_driver.cpp" -o "$OUT/lrc_scalar_gpp"
timeout 30 "$OUT/lrc_scalar_gpp" > "$OUT/scalar_gpp.out"

echo "== 4. clang++ -std=c++20 -fsanitize=undefined,address =="
timeout 60 clang++ $COMMON_CXX -fsanitize=undefined,address -DTQBE_CATCH_UB \
  "$OUT/lrc_driver.cpp" -o "$OUT/lrc_asan"
timeout 30 "$OUT/lrc_asan" > "$OUT/asan.out"
diff -u "$OUT/ref.out" "$OUT/asan.out"
timeout 60 clang++ $COMMON_CXX -fsanitize=undefined,address \
  "$OUT/lrc_scalar_driver.cpp" -o "$OUT/lrc_scalar_asan"
timeout 30 "$OUT/lrc_scalar_asan" > "$OUT/scalar_asan.out"
diff -u "$OUT/scalar_gpp.out" "$OUT/scalar_asan.out"

echo "== 5. native x64 codegen (x64Target + gcc) =="
timeout 120 lake env lean --run test/lrc/emit_x64.lean "$OUT/lrc_x64.s"
timeout 60 gcc -O1 -no-pie test/lrc/lrc_main.c "$OUT/lrc_x64.s" -o "$OUT/lrc_x64"
timeout 30 "$OUT/lrc_x64" > "$OUT/x64.out"
diff -u "$OUT/ref.out" "$OUT/x64.out"

echo "== 6. native Arm64 codegen (armTarget + aarch64-linux-gnu-gcc + qemu-aarch64) =="
timeout 120 lake env lean --run test/lrc/emit_arm64.lean "$OUT/lrc_arm64.s"
timeout 60 aarch64-linux-gnu-gcc -O1 test/lrc/lrc_main.c "$OUT/lrc_arm64.s" \
  -o "$OUT/lrc_arm64" 2>&1 | grep -v -e 'SFrame' || true
timeout 30 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/lrc_arm64" > "$OUT/arm64.out"
diff -u "$OUT/ref.out" "$OUT/arm64.out"

if [ -z "${QBE:-}" ]; then
  _qbe_rc=0
  QBE="$("$ROOT/scripts/ensure_qbe.sh")" || _qbe_rc=$?
  if [ "$_qbe_rc" -ne 0 ] && [ "$_qbe_rc" -ne 2 ]; then
    exit "$_qbe_rc"
  fi
fi
if [ -n "${QBE:-}" ] && [ -x "${QBE:-}" ]; then
  echo "== 7. stock QBE cross-check (amd64_sysv + arm64) =="
  timeout 30 "$QBE" -t amd64_sysv -o "$OUT/lrc_qbe_x64.s" "$OUT/lrc.ssa"
  timeout 60 gcc -O1 -no-pie test/lrc/lrc_main.c "$OUT/lrc_qbe_x64.s" -o "$OUT/lrc_qbe_x64"
  timeout 30 "$OUT/lrc_qbe_x64" > "$OUT/qbe_x64.out"
  diff -u "$OUT/ref.out" "$OUT/qbe_x64.out"

  timeout 30 "$QBE" -t arm64 -o "$OUT/lrc_qbe_arm64.s" "$OUT/lrc.ssa"
  timeout 60 aarch64-linux-gnu-gcc -O1 test/lrc/lrc_main.c "$OUT/lrc_qbe_arm64.s" \
    -o "$OUT/lrc_qbe_arm64" 2>&1 | grep -v -e 'SFrame' || true
  timeout 30 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/lrc_qbe_arm64" > "$OUT/qbe_arm64.out"
  diff -u "$OUT/ref.out" "$OUT/qbe_arm64.out"
else
  echo "NOTE: stock QBE not found (set QBE, QBE_SRC, or place checkout at $ROOT/qbe); skipping step 7."
fi

echo "== test/lrc/run.sh: ALL DIFFERENTIAL CHECKS PASSED =="
cat "$OUT/ref.out"
