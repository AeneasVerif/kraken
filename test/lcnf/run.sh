#!/usr/bin/env bash
# Differential + performance suite for the impure LCNF -> LeanQbe.T pipeline (LeanQbe.T.LeanLCNF).
#
#  1. Builds the LCNF modules and LeanQbeTest.T.LeanLCNFTest (kernel `Func.Wf` theorems, #guards).
#  2. Builds native emitters (`lean -c` + `leanc` against the project's object files).
#  3. Writes the PrintCpp translation unit and stage-by-stage traces (.mono / .impure / LeanQbe.T /
#     x86-64 / Arm64) of representative functions into $OUT/trace.
#  4. Runs the demo programs (RBMap, mergeSort + closures, DPLL, ExprVM) on four backends and
#     compares their output bit for bit:
#       a. native Lean 4 (`lean -c` + `leanc -O2`) on the *same* source (extracted from Demo.lean),
#       b. PrintCpp + clang++ -std=c++20 -O2 -fsanitize=address,undefined (reduced sizes),
#       c. native x86-64 (LeanQbe.T.compile x64Target + gcc -O2),
#       d. native Arm64 (LeanQbe.T.compile armTarget + aarch64-linux-gnu-gcc -O2 + qemu-aarch64),
#     with the runtime's `live == persistent` zero-leak check after every call and the FBIP
#     in-place reuse assertion.
#  5. Benchmarks LeanQbe.T x86-64 against `leanc -O2` (wall clock + allocator telemetry).
# Every command runs under `timeout`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
T="$ROOT/test/lcnf"
KIR="${KRAKEN_IR:-$ROOT/.lake/build/ir}"

OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-lcnf.XXXXXX")}"
cleanup() { if [ -z "${KEEP_OUT:-}" ]; then rm -rf "$OUT"; fi; }
trap cleanup EXIT
mkdir -p "$OUT/bin" "$OUT/obj" "$OUT/trace"
echo "outputs in $OUT"

echo "== 1. build LeanLCNF + tests (Func.Wf theorems, #guards) =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 600 lake build --wfail LeanQbe.T.LeanLCNF.Demo LeanQbe.T.LeanLCNF.Coverage \
    LeanQbeTest.T.LeanLCNFTest LeanQbeTest.T.LcnfP5Test LeanQbeTest.T.LcnfAudit \
    LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Amd64.PrintATTAlign \
    LeanQbe.T.Arm64.Targ 2>&1 | tail -n 3
else
  echo "SKIP_BUILD=1: skipping lake build LeanLCNF + tests"
fi

echo "== 2. native emitters =="
# native_exe <exe> <lean source | -> <import>...: compile <lean source> natively (`-`: `main` is in
# an imported project module), linking the object files of every project / Kraken module in the
# import closure (built with `lake build +M:o`).
native_exe() {
  local exe="$1" src="$2"; shift 2
  { echo "import Lean"; for m in "$@"; do echo "import $m"; done
    echo 'open Lean in'
    echo '#eval show CoreM Unit from do'
    echo '  for n in (← getEnv).header.moduleNames do IO.println s!"MOD {n}"'
  } > "$OUT/closure_$exe.lean"
  timeout 300 lake env lean "$OUT/closure_$exe.lean" | sed -n 's/^MOD //p' > "$OUT/closure_$exe.txt"
  local mods objs=() m p o
  mods=$(grep -E '^LeanQbe(Test)?\.' "$OUT/closure_$exe.txt" || true)
  # shellcheck disable=SC2046
  timeout 900 lake build $(for m in $mods; do echo "+$m:o"; done) 2>&1 | tail -n 1
  for m in $mods; do objs+=("$ROOT/.lake/build/ir/$(echo "$m" | tr . /).c.o.export"); done
  for m in $(grep '^Kraken' "$OUT/closure_$exe.txt"); do
    p="$(echo "$m" | tr . /)"
    if [ -f "$KIR/$p.c.o.export" ]; then objs+=("$KIR/$p.c.o.export"); else
      o="$OUT/obj/$(echo "$m" | tr . _).o"
      timeout 300 leanc -c -O2 -DLEAN_EXPORTING "$KIR/$p.c" -o "$o"
      objs+=("$o")
    fi
  done
  if [ "$src" != - ]; then
    timeout 300 lake env lean -c "$OUT/obj/$exe.c" "$src"
    timeout 300 leanc -c -O2 "$OUT/obj/$exe.c" -o "$OUT/obj/$exe.o"
    objs+=("$OUT/obj/$exe.o")
  fi
  timeout 300 leanc -o "$OUT/bin/$exe" "${objs[@]}"
}
native_exe lcnf_test - LeanQbeTest.T.LeanLCNFTest
native_exe lcnf_p5_test - LeanQbeTest.T.LcnfP5Test

echo "== 3. PrintCpp TU, x86-64 / Arm64 assembly, stage-by-stage traces =="
timeout 120 "$OUT/bin/lcnf_test" "$OUT"
timeout 120 "$OUT/bin/lcnf_p5_test" "$OUT"
timeout 300 lake env lean --run test/common/emit.lean --arch x64 --suite lcnf "$OUT/lcnf_x64.s" "$OUT/lcnf_p5_x64.s"
timeout 300 lake env lean --run test/common/emit.lean --arch arm64 --suite lcnf "$OUT/lcnf_arm64.s" "$OUT/lcnf_p5_arm64.s"
# One function of an assembly file: from its label to the next function label.
asm_fn() {
  awk -v s="$1:" '$0 == s {p = 1} p && /^[A-Za-z_][A-Za-z0-9_]*:$/ && $0 != s {exit} p' "$2"
}
for f in RBNode_ins RBNode_mapValues mmerge dpll run sortBench__lam_5__boxed; do
  asm_fn "l_LeanQbe_T_LeanLCNF_Demo_$f" "$OUT/lcnf_x64.s" > "$OUT/trace/$f.x64.s"
  asm_fn "l_LeanQbe_T_LeanLCNF_Demo_$f" "$OUT/lcnf_arm64.s" > "$OUT/trace/$f.arm64.s"
done
tr="$OUT/trace/RBNode_ins"
echo "trace files: $(ls "$OUT/trace" | wc -l) in $OUT/trace" \
  "(e.g. $tr.{mono,impure,T.ssa,x64.s,arm64.s})"
echo "RBNode.ins: $(wc -l < "$tr.mono") mono -> $(wc -l < "$tr.impure") impure LCNF ->" \
  "$(wc -l < "$tr.T.ssa") LeanQbe.T -> $(wc -l < "$tr.x64.s") x86-64 /" \
  "$(wc -l < "$tr.arm64.s") Arm64 lines"

echo "== 4a. native Lean 4 oracle (lean -c + leanc -O2) on the extracted Demo.lean source =="
{ echo "namespace LeanQbe.T.LeanLCNF.Demo"
  sed -n '/^-- BEGIN LCNF DEMO$/,/^-- END LCNF DEMO$/p' LeanQbe/T/LeanLCNF/Demo.lean
  echo "end LeanQbe.T.LeanLCNF.Demo"
  cat "$T/ref_lean.lean"; } > "$OUT/ref_lean_full.lean"
(cd "$OUT" && timeout 120 lean -c ref_lean.c ref_lean_full.lean)
timeout 120 leanc -O2 "$OUT/ref_lean.c" -o "$OUT/ref_lean"
timeout 60 "$OUT/ref_lean" > "$OUT/ref.out"
timeout 60 "$OUT/ref_lean" quick > "$OUT/ref_quick.out"

CFLAGS_RT="-O2 -Wall -Wextra -Werror -I$T"
run_err() { # <stderr-file> <cmd...>
  local err="$1"; shift
  "$@" 2>"$err" || {
    local rc=$?
    tail -n 60 "$err" >&2 || true
    exit "$rc"
  }
}
check_run() { # <name> <stdout> <stderr> <expected>
  diff -u "$4" "$2" || { tail -n 60 "$3" >&2 || true; return 1; }
  if ! grep -q '^LEAKCHECK ok' "$3"; then
    tail -n 60 "$3" >&2 || true
    return 1
  fi
  echo "$1: $(wc -l < "$2") lines bit-identical to the oracle;" \
    "$(grep '^FBIP' "$3" || echo 'FBIP n/a'); $(grep '^STAT total' "$3")"
}

echo "== 4b. x86-64 (LeanQbe.T x64Target + gcc -O2) =="
timeout 120 gcc $CFLAGS_RT -no-pie "$T/lcnf_main.c" "$T/lcnf_rt.c" "$OUT/lcnf_x64.s" \
  -lm -o "$OUT/lcnf_x64"
run_err "$OUT/x64.err" timeout 60 "$OUT/lcnf_x64" > "$OUT/x64.out"
check_run x64 "$OUT/x64.out" "$OUT/x64.err" "$OUT/ref.out"

echo "== 4c. Arm64 (LeanQbe.T armTarget + aarch64-linux-gnu-gcc -O2 + qemu-aarch64) =="
timeout 120 aarch64-linux-gnu-gcc $CFLAGS_RT "$T/lcnf_main.c" "$T/lcnf_rt.c" \
  "$OUT/lcnf_arm64.s" -lm -o "$OUT/lcnf_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
run_err "$OUT/arm64.err" timeout 120 qemu-aarch64 -L /usr/aarch64-linux-gnu \
  "$OUT/lcnf_arm64" > "$OUT/arm64.out"
check_run arm64 "$OUT/arm64.out" "$OUT/arm64.err" "$OUT/ref.out"

echo "== 4d. PrintCpp + clang++ -std=c++20 -O2 -fsanitize=address,undefined (reduced sizes) =="
timeout 300 clang++ -std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined \
  -fno-sanitize-recover=all -DLCNF_TQBE -I"$ROOT/LeanQbe/T/Runtime" -I"$OUT" -I"$T" \
  -x c++ "$T/lcnf_main.c" -lm -o "$OUT/lcnf_cpp"
run_err "$OUT/cpp.err" timeout 120 "$OUT/lcnf_cpp" quick > "$OUT/cpp.out"
check_run printcpp-asan "$OUT/cpp.out" "$OUT/cpp.err" "$OUT/ref_quick.out"
if grep -E 'ERROR: AddressSanitizer|runtime error' "$OUT/cpp.err"; then exit 1; fi

echo "== 4e. P5 Coverage (strings, big Nats, Array, ByteArray, Float, Int, Int64, UIntN.ofBitVec," \
  "getObjTagNat, USize, non-ASCII symbols) across all 4 backends =="
{ echo "namespace LeanQbe.T.LeanLCNF.Coverage"
  sed -n '/^-- BEGIN LCNF COVERAGE$/,/^-- END LCNF COVERAGE$/p' LeanQbe/T/LeanLCNF/Coverage.lean
  echo "end LeanQbe.T.LeanLCNF.Coverage"
  cat "$T/ref_p5.lean"; } > "$OUT/ref_p5_full.lean"
(cd "$OUT" && timeout 120 lean -c ref_p5.c ref_p5_full.lean)
timeout 120 leanc -O2 "$OUT/ref_p5.c" -o "$OUT/ref_p5"
timeout 60 "$OUT/ref_p5" > "$OUT/ref_p5.out"
timeout 60 "$OUT/ref_p5" quick > "$OUT/ref_p5_quick.out"

timeout 120 gcc $CFLAGS_RT -no-pie "$T/lcnf_p5_main.c" "$T/lcnf_rt.c" "$OUT/lcnf_p5_x64.s" \
  -lm -o "$OUT/lcnf_p5_x64"
run_err "$OUT/p5_x64.err" timeout 60 "$OUT/lcnf_p5_x64" > "$OUT/p5_x64.out"
check_run p5-x64 "$OUT/p5_x64.out" "$OUT/p5_x64.err" "$OUT/ref_p5.out"

timeout 120 aarch64-linux-gnu-gcc $CFLAGS_RT "$T/lcnf_p5_main.c" "$T/lcnf_rt.c" \
  "$OUT/lcnf_p5_arm64.s" -lm -o "$OUT/lcnf_p5_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
run_err "$OUT/p5_arm64.err" timeout 120 qemu-aarch64 -L /usr/aarch64-linux-gnu \
  "$OUT/lcnf_p5_arm64" > "$OUT/p5_arm64.out"
check_run p5-arm64 "$OUT/p5_arm64.out" "$OUT/p5_arm64.err" "$OUT/ref_p5.out"

timeout 300 clang++ -std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined \
  -fno-sanitize-recover=all -DLCNF_TQBE -I"$ROOT/LeanQbe/T/Runtime" -I"$OUT" -I"$T" \
  -x c++ "$T/lcnf_p5_main.c" -lm -o "$OUT/lcnf_p5_cpp"
run_err "$OUT/p5_cpp.err" timeout 120 "$OUT/lcnf_p5_cpp" quick > "$OUT/p5_cpp.out"
check_run p5-printcpp-asan "$OUT/p5_cpp.out" "$OUT/p5_cpp.err" "$OUT/ref_p5_quick.out"
if grep -E 'ERROR: AddressSanitizer|runtime error' "$OUT/p5_cpp.err"; then exit 1; fi

echo "== 4f. lcnf_int_op fuzz vs __int128 (x86-64 ASan+UBSan, Arm64 qemu) =="
timeout 120 gcc -O1 -g -Wall -Wextra -Werror -fsanitize=address,undefined \
  -fno-sanitize-recover=all -I"$T" "$T/lcnf_int_test.c" "$T/lcnf_rt.c" -lm -o "$OUT/int_test_x64"
run_err "$OUT/int_x64.err" timeout 300 "$OUT/int_test_x64"
grep '^INTFUZZ' "$OUT/int_x64.err"
grep -q '^LEAKCHECK ok' "$OUT/int_x64.err"
timeout 120 aarch64-linux-gnu-gcc $CFLAGS_RT "$T/lcnf_int_test.c" "$T/lcnf_rt.c" -lm \
  -o "$OUT/int_test_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
run_err "$OUT/int_arm64.err" timeout 300 qemu-aarch64 -L /usr/aarch64-linux-gnu \
  "$OUT/int_test_arm64"
grep -q '^LEAKCHECK ok' "$OUT/int_arm64.err"
echo "int-fuzz: x64 + arm64 LEAKCHECK ok"

echo "== 5. benchmark: LeanQbe.T x86-64 vs leanc -O2 (wall clock ms) =="
timeout 120 "$OUT/ref_lean" bench > "$OUT/bench_ref.out"
run_err "$OUT/bench_x64.err" timeout 120 "$OUT/lcnf_x64" bench > "$OUT/bench_x64.out"
if ! grep -q '^LEAKCHECK ok' "$OUT/bench_x64.err"; then
  tail -n 60 "$OUT/bench_x64.err" >&2 || true
  exit 1
fi
printf '%-12s %12s %14s %8s  %s\n' workload "leanc -O2" "LeanQbe.T x64" ratio \
  "allocs/reused (LeanQbe.T runtime)"
join <(sort "$OUT/bench_ref.out" | awk '{print $2, $3, $4}') \
     <(sort "$OUT/bench_x64.out" | awk '{print $2, $3, $4}') | while read -r n tr rr tx rx; do
  [ "$rr" = "$rx" ] || { echo "FAIL bench result mismatch on $n: $rr vs $rx"; exit 1; }
  st=$(grep "^STAT $n " "$OUT/bench_x64.err" |
    sed 's/.*allocs=\([0-9]*\).*reused=\([0-9]*\).*/\1\/\2/')
  printf '%-12s %12.1f %14.1f %7.2fx  %s\n' "$n" "$tr" "$tx" "$(echo "$tx / $tr" | bc -l)" "$st"
done

echo "== test/lcnf/run.sh: ALL CHECKS PASSED =="
