#!/usr/bin/env bash
# C++20 differential & ASan/UBSan test suite for LeanQbe.T.Examples.LratBytes.
# Writes all generated C++ files and binaries to a temporary directory under /tmp/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-tlrat.XXXXXX")}"
echo "outputs in $OUT"

echo "== 1. build LratBytesLemmas & LratBytesTest, generate C++20 suite into $OUT =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 300 lake build --wfail LeanQbe.T.Examples.LratBytesLemmas LeanQbeTest.T.LratBytesTest
else
  echo "SKIP_BUILD=1: skipping lake build LratBytesLemmas + LratBytesTest"
fi
timeout 120 lake env lean --run LeanQbeTest/T/LratBytesTest.lean "$OUT"

RT_INC="$ROOT/LeanQbe/T/Runtime"
COMMON_FLAGS="-std=c++20 -O2 -Wall -Wextra -Werror -I$RT_INC -I$OUT"

for compiler in g++ clang++; do
  if ! command -v "$compiler" >/dev/null 2>&1; then
    echo "FAIL: $compiler not found"
    exit 1
  fi
  EXTRA=""
  if [ "$compiler" = "clang++" ]; then
    EXTRA="-fsanitize=undefined,address"
  fi
  echo "== 2. [$compiler] compile standalone TUs =="
  for tu in gen_lrat_mod.cpp gen_lrat_aarch64.cpp gen_lrat_avx2.cpp; do
    timeout 60 "$compiler" $COMMON_FLAGS $EXTRA -c "$OUT/$tu" -o "$OUT/$tu.$compiler.o"
  done
  echo "== 3. [$compiler] compile & run differential driver (-DTQBE_CATCH_UB) =="
  timeout 60 "$compiler" $COMMON_FLAGS $EXTRA -DTQBE_CATCH_UB "$OUT/gen_lrat_driver.cpp" -o "$OUT/lrat_driver_catch_$compiler"
  timeout 60 "$OUT/lrat_driver_catch_$compiler"
  echo "== 4. [$compiler] compile & run differential driver (default trap mode) =="
  timeout 60 "$compiler" $COMMON_FLAGS $EXTRA "$OUT/gen_lrat_driver.cpp" -o "$OUT/lrat_driver_trap_$compiler"
  timeout 60 "$OUT/lrat_driver_trap_$compiler"
done

echo "== test/t_lrat/run.sh: ALL PASSED =="
