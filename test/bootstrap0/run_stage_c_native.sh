#!/usr/bin/env bash
set -euo pipefail

# test/bootstrap0/run_stage_c_native.sh
# End-to-end native emission, execution & differential verification for Stage C.
#
# Matrix:
# 1. Native leanqbe0 AT&T assembly assembled with gcc & clang
# 2. Native full leanqbe AT&T assembly assembled with gcc & clang
# 3. Reference clang -O3 (C3b) object
# 4. Native test harness exercising arithmetic, multi-fn pipeline, loop,
#    memory swap/add, and SAT/LRAT literal & clause evaluation
# 5. Compile time & .text size comparison

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$ROOT"

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/stage_c_native.XXXXXX")}"
mkdir -p "$OUT"
cleanup() {
  if [ -z "$OUT_USER" ]; then
    rm -rf "$OUT"
  fi
}
trap cleanup EXIT

for tool in gcc clang size; do
  command -v "$tool" >/dev/null 2>&1 || {
    echo "FAIL: required tool not found: $tool" >&2
    exit 1
  }
done

echo "[1/5] Emitting Stage C assembly from LeanQbe..."
cat > "$OUT/emit_stage_c.lean" <<'EOF'
import LeanQbe.T.Bootstrap0.StageC
import LeanQbe.T.Bootstrap0.Compiler0
import LeanQbe.T.Bootstrap0.Bridge0
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Isa
import LeanQbe.T.Amd64.PrintAsm0
import Kraken.X64.PrintATT

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0
open LeanQbe.T.Frontend.C0

def main (args : List String) : IO UInt32 := do
  let outDir := args.headD "."
  -- 1. Emit leanqbe0 assembly from stageCSource
  let tfs0 ← match compileC0Source [] stageCSource with
    | .ok t => pure t
    | .error e =>
      IO.eprintln s!"compileC0Source failed: {e}"
      return 1
  let (mod0, tbl) ← match ofTFlatModule tfs0 [] [] with
    | .ok p => pure p
    | .error e =>
      IO.eprintln s!"ofTFlatModule failed: {e}"
      return 1
  let dirs0 ← match leanqbe0Compile mod0 with
    | .ok ds _ => pure ds
    | .err k sl =>
      IO.eprintln s!"leanqbe0Compile failed: {k} {sl}"
      return 1
  let fnNames := tfs0.map (·.name)
  let p := toAmd64Program (symNameOf tbl) dirs0
  let asm0 := printModule0 fnNames p
  IO.FS.writeFile s!"{outDir}/stage_c_leanqbe0.s" asm0
  let cPreamble := "typedef unsigned long long u64;\ntypedef unsigned char u8;\n"
  IO.FS.writeFile s!"{outDir}/stage_c.c" (cPreamble ++ stageCSource)

  -- 2. Emit full leanqbe assembly
  let fns := tfs0.map (·.toFn)
  let dirsFull ← match Driver.compileFns x64Isa x64LegalTarget fns with
    | .ok ds => pure ds
    | .error e =>
      IO.eprintln s!"Driver.compileFns failed: {e}"
      return 1
  let asmFull := printModule0 fnNames dirsFull
  IO.FS.writeFile s!"{outDir}/stage_c_full_leanqbe.s" asmFull
  return 0
EOF

timeout 120 lake env lean --run "$OUT/emit_stage_c.lean" "$OUT"

echo "[2/5] Compiling C reference (clang -O3 / C3b) and assembling assemblies..."
timeout 30 clang -O3 -c "$OUT/stage_c.c" -o "$OUT/stage_c_clang_O3.o"
timeout 30 gcc -c "$OUT/stage_c_leanqbe0.s" -o "$OUT/stage_c_lq0_gcc.o"
timeout 30 clang -c "$OUT/stage_c_leanqbe0.s" -o "$OUT/stage_c_lq0_clang.o"
timeout 30 gcc -c "$OUT/stage_c_full_leanqbe.s" -o "$OUT/stage_c_full_gcc.o"
timeout 30 clang -c "$OUT/stage_c_full_leanqbe.s" -o "$OUT/stage_c_full_clang.o"

echo "[3/5] Building differential native test harness..."
cat > "$OUT/test_harness.c" <<'EOF'
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

extern uint64_t c0_sqr(uint64_t x);
extern uint64_t c0_poly(uint64_t x, uint64_t a, uint64_t b, uint64_t c);
extern uint64_t c0_sumto(uint64_t n);
extern uint64_t c0_mem_swap_add(uint64_t *ptr_a, uint64_t *ptr_b);
extern uint64_t sat_lit_var(uint64_t lit);
extern uint64_t sat_lit_sign(uint64_t lit);
extern uint64_t sat_lit_neg(uint64_t lit);
extern uint64_t sat_eval_lit(uint64_t lit, uint8_t *assign_base);
extern uint64_t sat_check_clause2(uint64_t lit1, uint64_t lit2,
                                  uint8_t *assign_base);

int main(void) {
  // 1. Arithmetic & polynomial kernels
  assert(c0_sqr(0) == 0);
  assert(c0_sqr(7) == 49);
  assert(c0_sqr(12345) == 152399025ULL);
  assert(c0_poly(3, 2, 5, 7) == 40);
  assert(c0_poly(10, 1, 0, 5) == 105);

  // 2. Loop kernel
  assert(c0_sumto(0) == 0);
  assert(c0_sumto(10) == 55);
  assert(c0_sumto(100) == 5050);

  // 3. Memory pointer read/write/swap kernel
  uint64_t a = 1234, b = 5678;
  uint64_t sum_ab = c0_mem_swap_add(&a, &b);
  assert(sum_ab == 1234 + 5678);
  assert(a == 5678);
  assert(b == 1234);

  // 4. SAT/LRAT literal & clause helper kernel
  assert(sat_lit_var(0) == 0 && sat_lit_sign(0) == 0 && sat_lit_neg(0) == 1);
  assert(sat_lit_var(1) == 0 && sat_lit_sign(1) == 1 && sat_lit_neg(1) == 0);
  assert(sat_lit_var(6) == 3 && sat_lit_sign(6) == 0 && sat_lit_neg(6) == 7);
  assert(sat_lit_var(7) == 3 && sat_lit_sign(7) == 1 && sat_lit_neg(7) == 6);
  assert(sat_lit_var(42) == 21 && sat_lit_sign(42) == 0 && sat_lit_neg(42) == 43);

  // Assignment: var 1=1 (T), var 2=2 (F), var 3=1 (T)
  uint8_t assign[8] = {0, 1, 2, 1, 0, 0, 0, 0};
  assert(sat_eval_lit(6, assign) == 1); // var 3 pos -> true
  assert(sat_eval_lit(7, assign) == 2); // var 3 neg -> false
  assert(sat_eval_lit(4, assign) == 2); // var 2 pos -> false
  assert(sat_eval_lit(5, assign) == 1); // var 2 neg -> true
  assert(sat_eval_lit(8, assign) == 0); // var 4 pos -> undef

  // Clause 1: (v3 | v2) -> (lit 6 | lit 4) -> v3 is true -> 1 (sat)
  assert(sat_check_clause2(6, 4, assign) == 1);
  // Clause 2: (~v3 | v2) -> (lit 7 | lit 4) -> both false -> 2 (conflict)
  assert(sat_check_clause2(7, 4, assign) == 2);
  // Clause 3: (~v3 | v4) -> (lit 7 | lit 8) -> lit 7 false, lit 8 undef -> 0
  assert(sat_check_clause2(7, 8, assign) == 0);

  puts("ALL_NATIVE_TESTS_PASS");
  return 0;
}
EOF

# Link differential test matrix
timeout 30 gcc "$OUT/test_harness.c" "$OUT/stage_c_lq0_gcc.o" -o "$OUT/bin_lq0_gcc"
timeout 30 clang "$OUT/test_harness.c" "$OUT/stage_c_lq0_clang.o" -o "$OUT/bin_lq0_clang"
timeout 30 gcc "$OUT/test_harness.c" "$OUT/stage_c_full_gcc.o" -o "$OUT/bin_full_gcc"
timeout 30 clang "$OUT/test_harness.c" "$OUT/stage_c_full_clang.o" -o "$OUT/bin_full_clang"
timeout 30 clang "$OUT/test_harness.c" "$OUT/stage_c_clang_O3.o" -o "$OUT/bin_clang_O3"

echo "[4/5] Executing differential native test matrix..."
res1="$(timeout 30 "$OUT/bin_lq0_gcc")"
res2="$(timeout 30 "$OUT/bin_lq0_clang")"
res3="$(timeout 30 "$OUT/bin_full_gcc")"
res4="$(timeout 30 "$OUT/bin_full_clang")"
res5="$(timeout 30 "$OUT/bin_clang_O3")"

if [ "$res1" != "ALL_NATIVE_TESTS_PASS" ] || \
   [ "$res2" != "ALL_NATIVE_TESTS_PASS" ] || \
   [ "$res3" != "ALL_NATIVE_TESTS_PASS" ] || \
   [ "$res4" != "ALL_NATIVE_TESTS_PASS" ] || \
   [ "$res5" != "ALL_NATIVE_TESTS_PASS" ]; then
  echo "FAIL: differential execution output mismatch!" >&2
  exit 1
fi
echo "  leanqbe0 (gcc):   $res1"
echo "  leanqbe0 (clang): $res2"
echo "  full lqbe (gcc):  $res3"
echo "  full lqbe (clang):$res4"
echo "  clang -O3 (C3b):  $res5"

echo "[5/5] Measuring compile times & .text code sizes..."
cat > "$OUT/bench_compile.lean" <<'EOF'
import LeanQbe.T.Bootstrap0.StageC
import LeanQbe.T.Bootstrap0.Compiler0
import LeanQbe.T.Bootstrap0.Bridge0
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Isa
import LeanQbe.T.Amd64.PrintAsm0

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Bootstrap0
open LeanQbe.T.Frontend.C0

def main : IO Unit := do
  let tfs ← match compileC0Source [] stageCSource with
    | .ok t => pure t
    | .error e => throw <| IO.userError s!"c0: {e}"
  let (mod, _) ← match ofTFlatModule tfs [] [] with
    | .ok p => pure p
    | .error e => throw <| IO.userError s!"ofTFlat: {e}"
  let fns := tfs.map (·.toFn)

  -- Warm up
  let _ := leanqbe0Compile mod
  let _ := Driver.compileFns x64Isa x64LegalTarget fns

  -- Benchmark 1000 iterations
  let iters := 1000
  let t0 ← IO.monoNanosNow
  for _ in [:iters] do
    let _ := leanqbe0Compile mod
  let t1 ← IO.monoNanosNow

  let t2 ← IO.monoNanosNow
  for _ in [:iters] do
    let _ := Driver.compileFns x64Isa x64LegalTarget fns
  let t3 ← IO.monoNanosNow

  let lq0Nanos := t1 - t0
  let lqFullNanos := t3 - t2
  let lq0PerIterUs := (lq0Nanos.toFloat / iters.toFloat) / 1000.0
  let lqFullPerIterUs := (lqFullNanos.toFloat / iters.toFloat) / 1000.0
  IO.println s!"COMPILE_TIME: leanqbe0={lq0PerIterUs} us/iter, full={lqFullPerIterUs} us/iter"
EOF

timeout 60 lake env lean --run "$OUT/bench_compile.lean"

echo "OBJECT SIZES (.text section):"
size "$OUT/stage_c_lq0_gcc.o" "$OUT/stage_c_full_gcc.o" "$OUT/stage_c_clang_O3.o"

echo "PASS: Stage C end-to-end native emission & execution differential test succeeded!"
