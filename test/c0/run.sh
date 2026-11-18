#!/usr/bin/env bash
# C0 frontend V1 layout parity, C0/C99/C++20 compilation, and D2 differential test suite.
# Writes all generated C++ headers, object files, and binaries strictly under /tmp/.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-c0.XXXXXX")}"
echo "outputs in $OUT"

echo "== 1. build C0 frontend & C0Test, generate C++20 headers into $OUT =="
timeout 300 lake build --wfail LeanQbe.T.Frontend.C0 LeanQbeTest.T.C0Test
timeout 120 lake env lean --run LeanQbeTest/T/C0Test.lean "$OUT"

C99_FLAGS="-std=c99 -O2 -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror"
C11_FLAGS="-std=c11 -O2 -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror"
CPP_INC="-I$ROOT/LeanQbe/T/Runtime -I$ROOT/LeanQbe/T/Frontend/C0 -I$ROOT/test/c0 -I$OUT"
CPP_FLAGS="-std=c++20 -O2 -Wall -Wextra -Werror $CPP_INC"

echo "== 2. (V1) compile & run C99/C11 layout parity checks (gcc + clang ASan/UBSan) =="
timeout 60 gcc $C99_FLAGS "$ROOT/test/c0/test_layout_check.c" -o "$OUT/layout_gcc_c99"
timeout 60 "$OUT/layout_gcc_c99"
timeout 60 gcc $C11_FLAGS "$ROOT/test/c0/test_layout_check.c" -o "$OUT/layout_gcc_c11"
timeout 60 "$OUT/layout_gcc_c11"
timeout 60 clang $C99_FLAGS -fsanitize=undefined,address "$ROOT/test/c0/test_layout_check.c" -o "$OUT/layout_clang"
timeout 60 "$OUT/layout_clang"

cat > "$OUT/d2_main.cpp" <<'EOF'
#include "c0.h"
#include "d2_diff.h"
int main() { return run_d2_tests(); }
EOF

echo "== 3. (D2) compile native C99 fixtures & run C++20 differential suite (gcc+g++ and clang+clang++ ASan/UBSan) =="
for cc_pair in "gcc:g++:" "clang:clang++:-fsanitize=undefined,address"; do
  IFS=':' read -r CC CXX EXTRA <<< "$cc_pair"
  echo "--- [$CC / $CXX ${EXTRA:-O2}] ---"
  for src in test_layout.c proplit.c lean_rc.c extra_cf.c; do
    timeout 60 "$CC" $C99_FLAGS $EXTRA -c "$ROOT/test/c0/$src" -o "$OUT/${src%.c}.$CC.o"
  done
  timeout 60 "$CXX" $CPP_FLAGS $EXTRA \
    "$OUT/d2_main.cpp" \
    "$OUT/test_layout.$CC.o" \
    "$OUT/proplit.$CC.o" \
    "$OUT/lean_rc.$CC.o" \
    "$OUT/extra_cf.$CC.o" \
    -o "$OUT/d2_runner_$CXX"
  timeout 60 "$OUT/d2_runner_$CXX"
done

echo "== test/c0/run.sh: ALL PASSED =="
