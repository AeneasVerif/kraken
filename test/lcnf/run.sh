#!/usr/bin/env bash
# Differential + performance suite for the impure LCNF -> LeanQbe.T pipeline (LeanQbe.T.LeanLCNF).
#
#  1. Builds the LCNF modules and LeanQbeTest.T.LeanLCNFTest (kernel `Func.Wf` theorems, #guards).
#  2. Builds native emitters (`lean -c` + `leanc` against the project's object files) in one
#     union `lake build +M:o` pass for `lcnf_test`, `lcnf_p5_test`, `lcnf_emit_x64`, `lcnf_emit_arm64`.
#  3. Writes the PrintCpp translation unit, x86-64 / Arm64 assembly, and stage-by-stage traces
#     (.mono / .impure / LeanQbe.T / x86-64 / Arm64) into $OUT/trace in parallel.
#  4. Runs the demo & P5 coverage programs on four backends + lcnf_int_op fuzz in parallel and
#     compares their output bit for bit:
#       a. native Lean 4 (`lean -c` + `leanc -O2`) on the *same* source (extracted from Demo.lean),
#       b. PrintCpp + clang++ -std=c++20 -O2 -fsanitize=address,undefined (reduced sizes),
#       c. native x86-64 (LeanQbe.T.compile x64Target + gcc -O2),
#       d. native Arm64 (LeanQbe.T.compile armTarget + aarch64-linux-gnu-gcc -O2 + qemu-aarch64),
#     with the runtime's `live == persistent` zero-leak check after every call and the FBIP
#     in-place reuse assertion.
#  5. Benchmarks LeanQbe.T x86-64 against `leanc -O2` standalone (uncontended wall clock + telemetry).
# Every command runs under `timeout`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
T="$ROOT/test/lcnf"
KIR="${KRAKEN_IR:-$ROOT/.lake/build/ir}"

OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-lcnf.XXXXXX")}"
cleanup() { if [ -z "${KEEP_OUT:-}" ]; then rm -rf "$OUT"; fi; }
trap cleanup EXIT
mkdir -p "$OUT/bin" "$OUT/obj" "$OUT/trace" "$OUT/logs"
echo "outputs in $OUT"

echo "== 1. build LeanLCNF + tests (Func.Wf theorems, #guards) =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 600 lake build --wfail LeanQbe.T.LeanLCNF.Demo LeanQbe.T.LeanLCNF.Coverage \
    LeanQbeTest.T.LeanLCNFTest LeanQbeTest.T.LcnfP5Test LeanQbeTest.T.LcnfAudit \
    LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Amd64.PrintATTAlign \
    LeanQbe.T.Arm64.Targ Kraken.AArch64.Print 2>&1 | tail -n 3
else
  echo "SKIP_BUILD=1: skipping lake build LeanLCNF + tests"
fi

echo "== 2. native emitters (union closure build + native x64/Arm64 codegen) =="
cat > "$OUT/emit_lcnf_x64.lean" <<'EOF'
import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

private def emitOne (tag : String) (m : LcModule) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule m)
  let fns := LeanLRC.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints)
  IO.FS.writeFile out (Driver.emitAsm (fun c => toATTAligned c ++ "\n") fns dirs)
  IO.eprintln s!"emit_x64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "lcnf_x64.s"
  emitOne "demo" Demo.lcnfProgram out
  match args with
  | _ :: covOut :: _ => emitOne "cov" Coverage.covProgram covOut
  | _ => pure ()
EOF

cat > "$OUT/emit_lcnf_arm64.lean" <<'EOF'
import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

private def emitOne (tag : String) (m : LcModule) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let tfs ← IO.ofExcept (lowerModule m)
  let fns := LeanLRC.tflatFnsToFns tfs
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints)
  let pp := fun c =>
    ".p2align 2\n" ++ String.intercalate "\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile out (Driver.emitAsm (fun c => pp c ++ "\n") fns dirs)
  IO.eprintln s!"emit_arm64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms"

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "lcnf_arm64.s"
  emitOne "demo" Demo.lcnfProgram out
  match args with
  | _ :: covOut :: _ => emitOne "cov" Coverage.covProgram covOut
  | _ => pure ()
EOF

# Discover import closures for all 4 native executables in parallel.
probe_closure() {
  local exe="$1"; shift
  { echo "import Lean"; for m in "$@"; do echo "import $m"; done
    echo 'open Lean in'
    echo '#eval show CoreM Unit from do'
    echo '  for n in (← getEnv).header.moduleNames do IO.println s!"MOD {n}"'
  } > "$OUT/closure_$exe.lean"
  timeout 300 lake env lean "$OUT/closure_$exe.lean" | sed -n 's/^MOD //p' > "$OUT/closure_$exe.txt"
}

probe_closure lcnf_test LeanQbeTest.T.LeanLCNFTest &
pid_c1=$!
probe_closure lcnf_p5_test LeanQbeTest.T.LcnfP5Test &
pid_c2=$!
probe_closure lcnf_emit_x64 LeanQbe.T.LeanLCNF.Lower1 LeanQbe.T.LeanLCNF.Demo \
  LeanQbe.T.LeanLCNF.Coverage LeanQbe.T.Driver LeanQbe.T.Amd64.Targ \
  LeanQbe.T.Amd64.PrintATTAlign &
pid_c3=$!
probe_closure lcnf_emit_arm64 LeanQbe.T.LeanLCNF.Lower1 LeanQbe.T.LeanLCNF.Demo \
  LeanQbe.T.LeanLCNF.Coverage LeanQbe.T.Driver LeanQbe.T.Arm64.Targ \
  Kraken.AArch64.Print &
pid_c4=$!
wait "$pid_c1"; wait "$pid_c2"; wait "$pid_c3"; wait "$pid_c4"

# One union `lake build +M:o` across all 4 closures (LeanQbe* + any missing Kraken* objects).
mapfile -t union_leanqbe < <(
  grep -h -E '^LeanQbe(Test)?\.' "$OUT"/closure_*.txt | sort -u
)
mapfile -t union_kraken < <(
  grep -h '^Kraken' "$OUT"/closure_*.txt | sort -u || true
)

lake_o_targets=()
for m in "${union_leanqbe[@]}"; do
  lake_o_targets+=("+$m:o")
done
for m in "${union_kraken[@]}"; do
  p="$(echo "$m" | tr . /)"
  if [ ! -f "$KIR/$p.c.o.export" ]; then
    lake_o_targets+=("+$m:o")
  fi
done
if [ "${#lake_o_targets[@]}" -gt 0 ]; then
  timeout 900 lake build "${lake_o_targets[@]}" 2>&1 | tail -n 1
fi

# Fallback: compile any still-missing Kraken .c into shared $OUT/obj/ once in parallel.
kraken_pids=()
for m in "${union_kraken[@]}"; do
  p="$(echo "$m" | tr . /)"
  if [ ! -f "$KIR/$p.c.o.export" ]; then
    o="$OUT/obj/$(echo "$m" | tr . _).o"
    timeout 300 leanc -c -O2 -DLEAN_EXPORTING "$KIR/$p.c" -o "$o" &
    kraken_pids+=($!)
  fi
done
for pid in "${kraken_pids[@]}"; do wait "$pid"; done

link_native_exe() {
  local exe="$1" src="$2"
  local objs=() m p o
  while IFS= read -r m; do
    [ -n "$m" ] || continue
    objs+=("$ROOT/.lake/build/ir/$(echo "$m" | tr . /).c.o.export")
  done < <(grep -E '^LeanQbe(Test)?\.' "$OUT/closure_$exe.txt" || true)
  while IFS= read -r m; do
    [ -n "$m" ] || continue
    p="$(echo "$m" | tr . /)"
    if [ -f "$KIR/$p.c.o.export" ]; then
      objs+=("$KIR/$p.c.o.export")
    else
      objs+=("$OUT/obj/$(echo "$m" | tr . _).o")
    fi
  done < <(grep '^Kraken' "$OUT/closure_$exe.txt" || true)
  if [ "$src" != - ]; then
    timeout 300 lake env lean -R "$OUT" -c "$OUT/obj/$exe.c" "$src"
    timeout 300 leanc -c -O2 "$OUT/obj/$exe.c" -o "$OUT/obj/$exe.o"
    objs+=("$OUT/obj/$exe.o")
  fi
  timeout 300 leanc -o "$OUT/bin/$exe" "${objs[@]}"
}

link_native_exe lcnf_test - &
pid_l1=$!
link_native_exe lcnf_p5_test - &
pid_l2=$!
link_native_exe lcnf_emit_x64 "$OUT/emit_lcnf_x64.lean" &
pid_l3=$!
link_native_exe lcnf_emit_arm64 "$OUT/emit_lcnf_arm64.lean" &
pid_l4=$!
wait "$pid_l1"; wait "$pid_l2"; wait "$pid_l3"; wait "$pid_l4"

echo "== 3. PrintCpp TU, native x86-64 / Arm64 assembly, stage-by-stage traces (parallel) =="
timeout 120 "$OUT/bin/lcnf_test" "$OUT" &
pid_e1=$!
timeout 120 "$OUT/bin/lcnf_p5_test" "$OUT" &
pid_e2=$!
timeout 120 "$OUT/bin/lcnf_emit_x64" "$OUT/lcnf_x64.s" "$OUT/lcnf_p5_x64.s" &
pid_e3=$!
timeout 120 "$OUT/bin/lcnf_emit_arm64" "$OUT/lcnf_arm64.s" "$OUT/lcnf_p5_arm64.s" &
pid_e4=$!
wait "$pid_e1"; wait "$pid_e2"; wait "$pid_e3"; wait "$pid_e4"

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

echo "== 4. parallel differential verification (4a-4f: oracles, x64, Arm64, PrintCpp ASan, P5, int-fuzz) =="
job_names=()
job_pids=()
launch_job() {
  local name="$1"; shift
  "$@" >"$OUT/logs/$name.log" 2>&1 &
  job_names+=("$name")
  job_pids+=($!)
}

job_ref_lean() {
  { echo "namespace LeanQbe.T.LeanLCNF.Demo"
    sed -n '/^-- BEGIN LCNF DEMO$/,/^-- END LCNF DEMO$/p' LeanQbe/T/LeanLCNF/Demo.lean
    echo "end LeanQbe.T.LeanLCNF.Demo"
    cat "$T/ref_lean.lean"; } > "$OUT/ref_lean_full.lean"
  (cd "$OUT" && timeout 120 lean -c ref_lean.c ref_lean_full.lean)
  timeout 120 leanc -O2 "$OUT/ref_lean.c" -o "$OUT/ref_lean"
  timeout 60 "$OUT/ref_lean" > "$OUT/ref.out"
  timeout 60 "$OUT/ref_lean" quick > "$OUT/ref_quick.out"
}

job_x64() {
  timeout 120 gcc $CFLAGS_RT -no-pie "$T/lcnf_main.c" "$T/lcnf_rt.c" "$OUT/lcnf_x64.s" \
    -lm -o "$OUT/lcnf_x64"
  run_err "$OUT/x64.err" timeout 60 "$OUT/lcnf_x64" > "$OUT/x64.out"
}

job_arm64() {
  timeout 120 aarch64-linux-gnu-gcc $CFLAGS_RT "$T/lcnf_main.c" "$T/lcnf_rt.c" \
    "$OUT/lcnf_arm64.s" -lm -o "$OUT/lcnf_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
  run_err "$OUT/arm64.err" timeout 120 qemu-aarch64 -L /usr/aarch64-linux-gnu \
    "$OUT/lcnf_arm64" > "$OUT/arm64.out"
}

job_printcpp_asan() {
  timeout 300 clang++ -std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined \
    -fno-sanitize-recover=all -DLCNF_TQBE -I"$ROOT/LeanQbe/T/Runtime" -I"$OUT" -I"$T" \
    -x c++ "$T/lcnf_main.c" -lm -o "$OUT/lcnf_cpp"
  run_err "$OUT/cpp.err" timeout 120 "$OUT/lcnf_cpp" quick > "$OUT/cpp.out"
}

job_ref_p5() {
  { echo "namespace LeanQbe.T.LeanLCNF.Coverage"
    sed -n '/^-- BEGIN LCNF COVERAGE$/,/^-- END LCNF COVERAGE$/p' LeanQbe/T/LeanLCNF/Coverage.lean
    echo "end LeanQbe.T.LeanLCNF.Coverage"
    cat "$T/ref_p5.lean"; } > "$OUT/ref_p5_full.lean"
  (cd "$OUT" && timeout 120 lean -c ref_p5.c ref_p5_full.lean)
  timeout 120 leanc -O2 "$OUT/ref_p5.c" -o "$OUT/ref_p5"
  timeout 60 "$OUT/ref_p5" > "$OUT/ref_p5.out"
  timeout 60 "$OUT/ref_p5" quick > "$OUT/ref_p5_quick.out"
}

job_p5_x64() {
  timeout 120 gcc $CFLAGS_RT -no-pie "$T/lcnf_p5_main.c" "$T/lcnf_rt.c" "$OUT/lcnf_p5_x64.s" \
    -lm -o "$OUT/lcnf_p5_x64"
  run_err "$OUT/p5_x64.err" timeout 60 "$OUT/lcnf_p5_x64" > "$OUT/p5_x64.out"
}

job_p5_arm64() {
  timeout 120 aarch64-linux-gnu-gcc $CFLAGS_RT "$T/lcnf_p5_main.c" "$T/lcnf_rt.c" \
    "$OUT/lcnf_p5_arm64.s" -lm -o "$OUT/lcnf_p5_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
  run_err "$OUT/p5_arm64.err" timeout 120 qemu-aarch64 -L /usr/aarch64-linux-gnu \
    "$OUT/lcnf_p5_arm64" > "$OUT/p5_arm64.out"
}

job_p5_printcpp_asan() {
  timeout 300 clang++ -std=c++20 -O2 -Wall -Wextra -Werror -fsanitize=address,undefined \
    -fno-sanitize-recover=all -DLCNF_TQBE -I"$ROOT/LeanQbe/T/Runtime" -I"$OUT" -I"$T" \
    -x c++ "$T/lcnf_p5_main.c" -lm -o "$OUT/lcnf_p5_cpp"
  run_err "$OUT/p5_cpp.err" timeout 120 "$OUT/lcnf_p5_cpp" quick > "$OUT/p5_cpp.out"
}

job_int_x64() {
  timeout 120 gcc -O1 -g -Wall -Wextra -Werror -fsanitize=address,undefined \
    -fno-sanitize-recover=all -I"$T" "$T/lcnf_int_test.c" "$T/lcnf_rt.c" -lm -o "$OUT/int_test_x64"
  run_err "$OUT/int_x64.err" timeout 300 "$OUT/int_test_x64"
}

job_int_arm64() {
  timeout 120 aarch64-linux-gnu-gcc $CFLAGS_RT "$T/lcnf_int_test.c" "$T/lcnf_rt.c" -lm \
    -o "$OUT/int_test_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
  run_err "$OUT/int_arm64.err" timeout 300 qemu-aarch64 -L /usr/aarch64-linux-gnu \
    "$OUT/int_test_arm64"
}

launch_job ref_lean job_ref_lean
launch_job x64 job_x64
launch_job arm64 job_arm64
launch_job printcpp_asan job_printcpp_asan
launch_job ref_p5 job_ref_p5
launch_job p5_x64 job_p5_x64
launch_job p5_arm64 job_p5_arm64
launch_job p5_printcpp_asan job_p5_printcpp_asan
launch_job int_x64 job_int_x64
launch_job int_arm64 job_int_arm64

step4_fail=0
for i in "${!job_pids[@]}"; do
  if ! wait "${job_pids[$i]}"; then
    echo "FAIL: parallel step4 job '${job_names[$i]}' failed:" >&2
    cat "$OUT/logs/${job_names[$i]}.log" >&2 || true
    step4_fail=1
  fi
done
if [ "$step4_fail" -ne 0 ]; then
  exit 1
fi

echo "== 4b-4d. Demo differential checks (x64, Arm64, PrintCpp ASan/UBSan vs Lean 4 oracle) =="
check_run x64 "$OUT/x64.out" "$OUT/x64.err" "$OUT/ref.out"
check_run arm64 "$OUT/arm64.out" "$OUT/arm64.err" "$OUT/ref.out"
check_run printcpp-asan "$OUT/cpp.out" "$OUT/cpp.err" "$OUT/ref_quick.out"
if grep -E 'ERROR: AddressSanitizer|runtime error' "$OUT/cpp.err"; then exit 1; fi

echo "== 4e. P5 Coverage differential checks across all 4 backends =="
check_run p5-x64 "$OUT/p5_x64.out" "$OUT/p5_x64.err" "$OUT/ref_p5.out"
check_run p5-arm64 "$OUT/p5_arm64.out" "$OUT/p5_arm64.err" "$OUT/ref_p5.out"
check_run p5-printcpp-asan "$OUT/p5_cpp.out" "$OUT/p5_cpp.err" "$OUT/ref_p5_quick.out"
if grep -E 'ERROR: AddressSanitizer|runtime error' "$OUT/p5_cpp.err"; then exit 1; fi

echo "== 4f. lcnf_int_op fuzz vs __int128 (x86-64 ASan+UBSan, Arm64 qemu) =="
grep '^INTFUZZ' "$OUT/int_x64.err"
grep -q '^LEAKCHECK ok' "$OUT/int_x64.err"
grep -q '^LEAKCHECK ok' "$OUT/int_arm64.err"
echo "int-fuzz: x64 + arm64 LEAKCHECK ok"

echo "== 5. benchmark: LeanQbe.T x86-64 vs leanc -O2 (standalone uncontended wall clock ms) =="
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
