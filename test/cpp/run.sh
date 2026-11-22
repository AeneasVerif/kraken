#!/usr/bin/env bash
# C++20 differential & Rule A6 trap-default test suite for LeanQbe.T.PrintCpp.
# Writes all generated C++ files and binaries to a temporary directory under /tmp/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-cpp.XXXXXX")}"
echo "outputs in $OUT"

echo "== 1. build PrintCppTest & generate C++ TUs into $OUT =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 300 lake build --wfail LeanQbe.T.PrintCpp LeanQbeTest.T.PrintCppTest
else
  echo "SKIP_BUILD=1: skipping lake build LeanQbe.T.PrintCpp LeanQbeTest.T.PrintCppTest"
fi
timeout 120 lake env lean --run LeanQbeTest/T/PrintCppTest.lean "$OUT"

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
  for tu in gen_standalone_uf.cpp gen_standalone_uf_avx2.cpp gen_standalone_edge.cpp gen_standalone_edge_aarch64.cpp; do
    timeout 60 "$compiler" $COMMON_FLAGS $EXTRA -c "$OUT/$tu" -o "$OUT/$tu.$compiler.o"
  done
  echo "== 3. [$compiler] compile & run test_catch_ub (-DTQBE_CATCH_UB) =="
  timeout 60 "$compiler" $COMMON_FLAGS $EXTRA -DTQBE_CATCH_UB "$ROOT/test/cpp/test_catch_ub.cpp" -o "$OUT/test_catch_ub_$compiler"
  timeout 60 "$OUT/test_catch_ub_$compiler"
  echo "== 4. [$compiler] compile & run test_trap_default (Rule A6 __builtin_trap default) =="
  timeout 60 "$compiler" $COMMON_FLAGS $EXTRA "$ROOT/test/cpp/test_trap_default.cpp" -o "$OUT/test_trap_default_$compiler"
  timeout 60 "$OUT/test_trap_default_$compiler"
done

echo "== test/cpp/run.sh: ALL PASSED =="
