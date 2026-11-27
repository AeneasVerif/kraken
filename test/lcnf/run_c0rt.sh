#!/usr/bin/env bash
# Compiled-C0-Runtime Differential Lane for LeanQbe.T.LeanLCNF (`rtC0CoreMod`).
#
# Unlike the Tier-0 C runtime lane (`test/lcnf/lcnf_rt.c`), this lane:
#   1. Compiles the verified 86-function pure-C0 runtime (`rtC0CoreMod` from
#      `LeanQbe.T.LeanLCNF.LcnfC0Full`) to native x86-64 and AArch64 `.s` / `.o` via
#      `LeanQbe.T.compile` (zero `lcnf_rt.c` runtime functions in the binary; only the
#      5-function host slab/panic shim `test/lcnf/lcnf_c0rt_shim.c` is linked).
#   2. Compiles float-free LCNF test programs (`Demo.lcnfProgram`, float-free
#      `Coverage`, `LcnfC0Demo.demoNatStrProgMod`) to x86-64 and AArch64 assembly.
#   3. Links all float-free programs + `lcnf_int_test.c` directly against `rt_c0_x64.o`
#      and `rt_c0_arm64.o` and runs them natively on x86-64 and under `qemu-aarch64`.
#   4. Checks bit-for-bit stdout, exit-code (0 and `lcnf_panic` exit 4), FBIP reuse,
#      100,000-iter `__int128` fuzz, and `live == persistent` leak parity against the
#      Lean 4 / `lcnf_rt.c` reference outputs.
# Every command runs under `timeout`.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"
T="$ROOT/test/lcnf"
KIR="${KRAKEN_IR:-$ROOT/.lake/build/ir}"

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-c0rt.XXXXXX")}"
cleanup() { if [ -z "$OUT_USER" ] && [ -z "${KEEP_OUT:-}" ]; then rm -rf "$OUT"; fi; }
trap cleanup EXIT
mkdir -p "$OUT/bin" "$OUT/obj" "$OUT/logs"
echo "c0rt outputs in $OUT"

echo "== c0rt 1. build LcnfC0Full + LcnfC0Demo + LeanLCNF emitters =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 600 lake build --wfail \
    LeanQbe.T.LeanLCNF.LcnfC0Full LeanQbe.T.LeanLCNF.LcnfC0Demo \
    LeanQbe.T.LeanLCNF.Demo LeanQbe.T.LeanLCNF.Coverage \
    LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Amd64.PrintATTAlign \
    LeanQbe.T.Arm64.Targ Kraken.AArch64.Print 2>&1 | tail -n 3
else
  echo "SKIP_BUILD=1: skipping lake build"
fi

echo "== c0rt 2. build native x64/Arm64 emitters & emit rtC0CoreMod + float-free LCNF =="
cat > "$OUT/emit_c0rt_x64.lean" <<'EOF'
import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.LcnfC0Full
import LeanQbe.T.LeanLCNF.LcnfC0Demo
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Amd64

private def covNoFloatMod : LcModule :=
  let m := Coverage.covProgram
  let bad (n : String) : Bool := n.contains "floatBench" || n.contains "applyFloat"
  { m with
    roots := m.roots.filter (fun r => !bad r)
    decls := m.decls.filter (fun d => !bad d.name)
    externs := m.externs.filter (fun e => !e.name.startsWith "Float.") }

private def emitFns (tag : String) (fns : List Fn) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints)
  IO.FS.writeFile out (Driver.emitAsm (fun c => toATTAligned c ++ "\n") fns dirs)
  IO.eprintln s!"emit_c0rt_x64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms"

def main (args : List String) : IO Unit := do
  match args with
  | rtOut :: p5Out :: c0demoOut :: demoOut :: _ =>
    emitFns "rtC0Core" rtC0CoreMod.fns rtOut
    let covTfs ← IO.ofExcept (lowerModule covNoFloatMod)
    emitFns "cov_nofloat" (Frontend.C0.tflatFnsToFns covTfs) p5Out
    emitFns "c0demo" demoNatStrProgMod.fns c0demoOut
    if demoOut != "-" then
      let demoTfs ← IO.ofExcept (lowerModule Demo.lcnfProgram)
      emitFns "demo" (Frontend.C0.tflatFnsToFns demoTfs) demoOut
  | _ => throw (IO.userError "usage: emit_c0rt_x64 <rt.s> <p5_nf.s> <c0demo.s> <demo.s|->")
EOF

cat > "$OUT/emit_c0rt_arm64.lean" <<'EOF'
import LeanQbe.T.LeanLCNF.Lower1
import LeanQbe.T.LeanLCNF.LcnfC0Full
import LeanQbe.T.LeanLCNF.LcnfC0Demo
import LeanQbe.T.LeanLCNF.Demo
import LeanQbe.T.LeanLCNF.Coverage
import LeanQbe.T.Driver
import LeanQbe.T.Arm64.Targ
import Kraken.AArch64.Print

set_option autoImplicit false

open LeanQbe.T LeanQbe.T.LeanLCNF LeanQbe.T.Arm64

private def covNoFloatMod : LcModule :=
  let m := Coverage.covProgram
  let bad (n : String) : Bool := n.contains "floatBench" || n.contains "applyFloat"
  { m with
    roots := m.roots.filter (fun r => !bad r)
    decls := m.decls.filter (fun d => !bad d.name)
    externs := m.externs.filter (fun e => !e.name.startsWith "Float.") }

private def emitFns (tag : String) (fns : List Fn) (out : System.FilePath) : IO Unit := do
  let t0 ← IO.monoMsNow
  let hints := fns.map (Fn.computeHints armTarget.toIsa armLegalTarget)
  let dirs ← IO.ofExcept (LeanQbe.T.compile armTarget.toIsa armLegalTarget fns hints)
  let pp := fun c =>
    ".p2align 2\n" ++ String.intercalate "\n" (c.map Kraken.AArch64.Print.directive)
  IO.FS.writeFile out (Driver.emitAsm (fun c => pp c ++ "\n") fns dirs)
  IO.eprintln s!"emit_c0rt_arm64 ({tag}): {fns.length} functions in {(← IO.monoMsNow) - t0} ms"

def main (args : List String) : IO Unit := do
  match args with
  | rtOut :: p5Out :: c0demoOut :: demoOut :: _ =>
    emitFns "rtC0Core" rtC0CoreMod.fns rtOut
    let covTfs ← IO.ofExcept (lowerModule covNoFloatMod)
    emitFns "cov_nofloat" (Frontend.C0.tflatFnsToFns covTfs) p5Out
    emitFns "c0demo" demoNatStrProgMod.fns c0demoOut
    if demoOut != "-" then
      let demoTfs ← IO.ofExcept (lowerModule Demo.lcnfProgram)
      emitFns "demo" (Frontend.C0.tflatFnsToFns demoTfs) demoOut
  | _ => throw (IO.userError "usage: emit_c0rt_arm64 <rt.s> <p5_nf.s> <c0demo.s> <demo.s|->")
EOF

probe_closure() {
  local exe="$1"; shift
  { echo "import Lean"; for m in "$@"; do echo "import $m"; done
    echo 'open Lean in'
    echo '#eval show CoreM Unit from do'
    echo '  for n in (← getEnv).header.moduleNames do IO.println s!"MOD {n}"'
  } > "$OUT/closure_$exe.lean"
  timeout 300 lake env lean "$OUT/closure_$exe.lean" | sed -n 's/^MOD //p' > "$OUT/closure_$exe.txt"
}

probe_closure c0rt_emit_x64 LeanQbe.T.LeanLCNF.Lower1 LeanQbe.T.LeanLCNF.LcnfC0Full \
  LeanQbe.T.LeanLCNF.LcnfC0Demo LeanQbe.T.LeanLCNF.Demo LeanQbe.T.LeanLCNF.Coverage \
  LeanQbe.T.Driver LeanQbe.T.Amd64.Targ LeanQbe.T.Amd64.PrintATTAlign &
pid_c1=$!
probe_closure c0rt_emit_arm64 LeanQbe.T.LeanLCNF.Lower1 LeanQbe.T.LeanLCNF.LcnfC0Full \
  LeanQbe.T.LeanLCNF.LcnfC0Demo LeanQbe.T.LeanLCNF.Demo LeanQbe.T.LeanLCNF.Coverage \
  LeanQbe.T.Driver LeanQbe.T.Arm64.Targ Kraken.AArch64.Print &
pid_c2=$!
wait "$pid_c1"; wait "$pid_c2"

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
  local objs=() m p
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
  timeout 300 lake env lean -R "$OUT" -c "$OUT/obj/$exe.c" "$src"
  timeout 300 leanc -c -O2 "$OUT/obj/$exe.c" -o "$OUT/obj/$exe.o"
  objs+=("$OUT/obj/$exe.o")
  timeout 300 leanc -o "$OUT/bin/$exe" "${objs[@]}"
}

link_native_exe c0rt_emit_x64 "$OUT/emit_c0rt_x64.lean" &
pid_l1=$!
link_native_exe c0rt_emit_arm64 "$OUT/emit_c0rt_arm64.lean" &
pid_l2=$!
wait "$pid_l1"; wait "$pid_l2"

DEMO_X64_S="${LCNF_C0RT_DEMO_X64_S:-}"
DEMO_ARM64_S="${LCNF_C0RT_DEMO_ARM64_S:-}"
ARG_DEMO_X64="-"
ARG_DEMO_ARM64="-"
if [ -z "$DEMO_X64_S" ] || [ ! -f "$DEMO_X64_S" ]; then
  DEMO_X64_S="$OUT/lcnf_x64.s"
  ARG_DEMO_X64="$DEMO_X64_S"
fi
if [ -z "$DEMO_ARM64_S" ] || [ ! -f "$DEMO_ARM64_S" ]; then
  DEMO_ARM64_S="$OUT/lcnf_arm64.s"
  ARG_DEMO_ARM64="$DEMO_ARM64_S"
fi

timeout 120 "$OUT/bin/c0rt_emit_x64" \
  "$OUT/rt_c0_x64.s" "$OUT/lcnf_p5_nf_x64.s" "$OUT/lcnf_c0demo_x64.s" "$ARG_DEMO_X64" &
pid_e1=$!
timeout 120 "$OUT/bin/c0rt_emit_arm64" \
  "$OUT/rt_c0_arm64.s" "$OUT/lcnf_p5_nf_arm64.s" "$OUT/lcnf_c0demo_arm64.s" "$ARG_DEMO_ARM64" &
pid_e2=$!
wait "$pid_e1"; wait "$pid_e2"

echo "== c0rt 3. assemble rtC0CoreMod (.o) & verify ZERO lcnf_rt.c runtime functions in shim =="
CFLAGS_C0RT="-O2 -Wall -Wextra -Werror -DLCNF_C0RT -I$T"
timeout 60 gcc -c "$OUT/rt_c0_x64.s" -o "$OUT/rt_c0_x64.o" &
pid_a1=$!
timeout 60 aarch64-linux-gnu-gcc -c "$OUT/rt_c0_arm64.s" -o "$OUT/rt_c0_arm64.o" &
pid_a2=$!
timeout 60 gcc $CFLAGS_C0RT -c "$T/lcnf_c0rt_shim.c" -o "$OUT/c0rt_shim_x64.o" &
pid_a3=$!
timeout 60 aarch64-linux-gnu-gcc $CFLAGS_C0RT -c "$T/lcnf_c0rt_shim.c" -o "$OUT/c0rt_shim_arm64.o" &
pid_a4=$!
wait "$pid_a1"; wait "$pid_a2"; wait "$pid_a3"; wait "$pid_a4"

shim_syms="$(nm -g --defined-only "$OUT/c0rt_shim_x64.o" | awk '{print $NF}' | sort | tr '\n' ' ')"
expected_shim_syms="lcnf_panic lcnf_rt_free lcnf_rt_init lcnf_rt_print_stats lcnf_state "
if [ "$shim_syms" != "$expected_shim_syms" ]; then
  echo "FAIL: unexpected symbols in c0rt_shim_x64.o: $shim_syms" >&2
  exit 1
fi
rt_x64_cnt="$(nm -g --defined-only "$OUT/rt_c0_x64.o" | wc -l)"
rt_arm64_cnt="$(aarch64-linux-gnu-nm -g --defined-only "$OUT/rt_c0_arm64.o" | wc -l)"
if [ "$rt_x64_cnt" -ne 86 ] || [ "$rt_arm64_cnt" -ne 86 ]; then
  echo "FAIL: expected 86 exported rtC0CoreMod fns (got x64=$rt_x64_cnt arm64=$rt_arm64_cnt)" >&2
  exit 1
fi
rt_x64_undef="$(nm -u "$OUT/rt_c0_x64.o" | awk '{print $NF}' | tr '\n' ' ')"
rt_arm64_undef="$(aarch64-linux-gnu-nm -u "$OUT/rt_c0_arm64.o" | awk '{print $NF}' | tr '\n' ' ')"
if [ "$rt_x64_undef" != "lcnf_panic " ] || [ "$rt_arm64_undef" != "lcnf_panic " ]; then
  echo "FAIL: unexpected rtC0CoreMod undefs (x64='$rt_x64_undef' arm64='$rt_arm64_undef')" >&2
  exit 1
fi
echo "symbol check OK: shim=5 host symbols (0 lcnf_rt.c runtime fns); rt_c0_x64.o=86 fns; rt_c0_arm64.o=86 fns"

echo "== c0rt 4. parallel native x64 + Arm64 QEMU differential runs =="
job_names=()
job_pids=()
launch_job() {
  local name="$1"; shift
  "$@" >"$OUT/logs/$name.log" 2>&1 &
  job_names+=("$name")
  job_pids+=($!)
}
run_err() {
  local err="$1"; shift
  "$@" 2>"$err" || {
    local rc=$?
    tail -n 60 "$err" >&2 || true
    exit "$rc"
  }
}

REF_OUT="${LCNF_C0RT_REF_OUT:-}"
if [ -n "$REF_OUT" ] && [ -f "$REF_OUT" ]; then
  cp "$REF_OUT" "$OUT/ref.out"
else
  job_ref_lean() {
    { echo "namespace LeanQbe.T.LeanLCNF.Demo"
      sed -n '/^-- BEGIN LCNF DEMO$/,/^-- END LCNF DEMO$/p' LeanQbe/T/LeanLCNF/Demo.lean
      echo "end LeanQbe.T.LeanLCNF.Demo"
      cat "$T/ref_lean.lean"; } > "$OUT/ref_lean_full.lean"
    (cd "$OUT" && timeout 120 lean -c ref_lean.c ref_lean_full.lean)
    timeout 120 leanc -O2 "$OUT/ref_lean.c" -o "$OUT/ref_lean"
    timeout 60 "$OUT/ref_lean" > "$OUT/ref.out"
  }
  launch_job ref_lean job_ref_lean
fi

REF_P5_OUT="${LCNF_C0RT_REF_P5_OUT:-}"
if [ -n "$REF_P5_OUT" ] && [ -f "$REF_P5_OUT" ]; then
  grep -v '^FLT ' "$REF_P5_OUT" > "$OUT/ref_p5_nf.out"
else
  job_ref_p5() {
    { echo "namespace LeanQbe.T.LeanLCNF.Coverage"
      sed -n '/^-- BEGIN LCNF COVERAGE$/,/^-- END LCNF COVERAGE$/p' LeanQbe/T/LeanLCNF/Coverage.lean
      echo "end LeanQbe.T.LeanLCNF.Coverage"
      cat "$T/ref_p5.lean"; } > "$OUT/ref_p5_full.lean"
    (cd "$OUT" && timeout 120 lean -c ref_p5.c ref_p5_full.lean)
    timeout 120 leanc -O2 "$OUT/ref_p5.c" -o "$OUT/ref_p5"
    timeout 60 "$OUT/ref_p5" | grep -v '^FLT ' > "$OUT/ref_p5_nf.out"
  }
  launch_job ref_p5 job_ref_p5
fi

job_c0demo_ref() {
  timeout 120 gcc -O2 -Wall -Wextra -Werror -no-pie -I"$T" \
    "$T/lcnf_c0rt_demo_main.c" "$T/lcnf_rt.c" "$OUT/lcnf_c0demo_x64.s" -lm -o "$OUT/c0demo_ref"
  run_err "$OUT/c0demo_ref.err" timeout 60 "$OUT/c0demo_ref" > "$OUT/c0demo_ref.out"
  set +e
  timeout 30 "$OUT/c0demo_ref" --panic > /dev/null 2> "$OUT/c0demo_ref_panic.err"
  local prc=$?
  set -e
  echo "$prc" > "$OUT/c0demo_ref_panic.rc"
  [ "$prc" -eq 4 ] || { echo "FAIL c0demo_ref --panic rc=$prc (expected 4)" >&2; exit 1; }
}

job_c0rt_demo_x64() {
  timeout 120 gcc $CFLAGS_C0RT -no-pie -Wl,-z,noexecstack \
    "$T/lcnf_main.c" "$DEMO_X64_S" "$OUT/rt_c0_x64.o" "$OUT/c0rt_shim_x64.o" \
    -o "$OUT/c0rt_demo_x64"
  run_err "$OUT/c0rt_demo_x64.err" timeout 60 "$OUT/c0rt_demo_x64" > "$OUT/c0rt_demo_x64.out"
}

job_c0rt_demo_arm64() {
  timeout 120 aarch64-linux-gnu-gcc $CFLAGS_C0RT -Wl,-z,noexecstack \
    "$T/lcnf_main.c" "$DEMO_ARM64_S" "$OUT/rt_c0_arm64.o" "$OUT/c0rt_shim_arm64.o" \
    -o "$OUT/c0rt_demo_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
  run_err "$OUT/c0rt_demo_arm64.err" timeout 120 qemu-aarch64 -L /usr/aarch64-linux-gnu \
    "$OUT/c0rt_demo_arm64" > "$OUT/c0rt_demo_arm64.out"
}

job_c0rt_p5_x64() {
  timeout 120 gcc $CFLAGS_C0RT -DLCNF_NO_FLOAT -no-pie -Wl,-z,noexecstack \
    "$T/lcnf_p5_main.c" "$OUT/lcnf_p5_nf_x64.s" "$OUT/rt_c0_x64.o" "$OUT/c0rt_shim_x64.o" \
    -o "$OUT/c0rt_p5_x64"
  run_err "$OUT/c0rt_p5_x64.err" timeout 60 "$OUT/c0rt_p5_x64" > "$OUT/c0rt_p5_x64.out"
}

job_c0rt_p5_arm64() {
  timeout 120 aarch64-linux-gnu-gcc $CFLAGS_C0RT -DLCNF_NO_FLOAT -Wl,-z,noexecstack \
    "$T/lcnf_p5_main.c" "$OUT/lcnf_p5_nf_arm64.s" "$OUT/rt_c0_arm64.o" "$OUT/c0rt_shim_arm64.o" \
    -o "$OUT/c0rt_p5_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
  run_err "$OUT/c0rt_p5_arm64.err" timeout 120 qemu-aarch64 -L /usr/aarch64-linux-gnu \
    "$OUT/c0rt_p5_arm64" > "$OUT/c0rt_p5_arm64.out"
}

job_c0rt_natstr_x64() {
  timeout 120 gcc $CFLAGS_C0RT -no-pie -Wl,-z,noexecstack \
    "$T/lcnf_c0rt_demo_main.c" "$OUT/lcnf_c0demo_x64.s" "$OUT/rt_c0_x64.o" "$OUT/c0rt_shim_x64.o" \
    -o "$OUT/c0rt_natstr_x64"
  run_err "$OUT/c0rt_natstr_x64.err" timeout 60 "$OUT/c0rt_natstr_x64" > "$OUT/c0rt_natstr_x64.out"
  set +e
  timeout 30 "$OUT/c0rt_natstr_x64" --panic > /dev/null 2> "$OUT/c0rt_natstr_x64_panic.err"
  local prc=$?
  set -e
  echo "$prc" > "$OUT/c0rt_natstr_x64_panic.rc"
}

job_c0rt_natstr_arm64() {
  timeout 120 aarch64-linux-gnu-gcc $CFLAGS_C0RT -Wl,-z,noexecstack \
    "$T/lcnf_c0rt_demo_main.c" "$OUT/lcnf_c0demo_arm64.s" "$OUT/rt_c0_arm64.o" "$OUT/c0rt_shim_arm64.o" \
    -o "$OUT/c0rt_natstr_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
  run_err "$OUT/c0rt_natstr_arm64.err" timeout 120 qemu-aarch64 -L /usr/aarch64-linux-gnu \
    "$OUT/c0rt_natstr_arm64" > "$OUT/c0rt_natstr_arm64.out"
  set +e
  timeout 30 qemu-aarch64 -L /usr/aarch64-linux-gnu "$OUT/c0rt_natstr_arm64" --panic \
    > /dev/null 2> "$OUT/c0rt_natstr_arm64_panic.err"
  local prc=$?
  set -e
  echo "$prc" > "$OUT/c0rt_natstr_arm64_panic.rc"
}

job_c0rt_int_x64() {
  timeout 120 gcc -O1 -g -Wall -Wextra -Werror -fsanitize=address,undefined \
    -fno-sanitize-recover=all -DLCNF_C0RT -no-pie -Wl,-z,noexecstack -I"$T" \
    "$T/lcnf_int_test.c" "$OUT/rt_c0_x64.o" "$OUT/c0rt_shim_x64.o" -o "$OUT/c0rt_int_x64"
  run_err "$OUT/c0rt_int_x64.err" timeout 300 "$OUT/c0rt_int_x64"
}

job_c0rt_int_arm64() {
  timeout 120 aarch64-linux-gnu-gcc $CFLAGS_C0RT -Wl,-z,noexecstack \
    "$T/lcnf_int_test.c" "$OUT/rt_c0_arm64.o" "$OUT/c0rt_shim_arm64.o" \
    -o "$OUT/c0rt_int_arm64" 2>&1 | { grep -v -e 'SFrame' || true; }
  run_err "$OUT/c0rt_int_arm64.err" timeout 300 qemu-aarch64 -L /usr/aarch64-linux-gnu \
    "$OUT/c0rt_int_arm64"
}

launch_job c0demo_ref job_c0demo_ref
launch_job c0rt_demo_x64 job_c0rt_demo_x64
launch_job c0rt_demo_arm64 job_c0rt_demo_arm64
launch_job c0rt_p5_x64 job_c0rt_p5_x64
launch_job c0rt_p5_arm64 job_c0rt_p5_arm64
launch_job c0rt_natstr_x64 job_c0rt_natstr_x64
launch_job c0rt_natstr_arm64 job_c0rt_natstr_arm64
launch_job c0rt_int_x64 job_c0rt_int_x64
launch_job c0rt_int_arm64 job_c0rt_int_arm64

fail=0
for i in "${!job_pids[@]}"; do
  if ! wait "${job_pids[$i]}"; then
    echo "FAIL: parallel c0rt job '${job_names[$i]}' failed:" >&2
    cat "$OUT/logs/${job_names[$i]}.log" >&2 || true
    fail=1
  fi
done
[ "$fail" -eq 0 ] || exit 1

check_run() {
  local name="$1" out="$2" err="$3" expected="$4"
  diff -u "$expected" "$out" || { tail -n 60 "$err" >&2 || true; return 1; }
  if ! grep -q '^LEAKCHECK ok' "$err"; then
    tail -n 60 "$err" >&2 || true
    return 1
  fi
  echo "$name: $(wc -l < "$out") lines bit-identical to oracle;" \
    "$(grep -E '^(FBIP|FBIP_ARR)' "$err" || echo 'FBIP n/a'); $(grep '^STAT ' "$err")"
}

echo "== c0rt 5. differential parity checks (x64 native + AArch64 QEMU) =="
check_run c0rt-demo-x64 "$OUT/c0rt_demo_x64.out" "$OUT/c0rt_demo_x64.err" "$OUT/ref.out"
check_run c0rt-demo-arm64 "$OUT/c0rt_demo_arm64.out" "$OUT/c0rt_demo_arm64.err" "$OUT/ref.out"
check_run c0rt-p5-x64 "$OUT/c0rt_p5_x64.out" "$OUT/c0rt_p5_x64.err" "$OUT/ref_p5_nf.out"
check_run c0rt-p5-arm64 "$OUT/c0rt_p5_arm64.out" "$OUT/c0rt_p5_arm64.err" "$OUT/ref_p5_nf.out"
check_run c0rt-natstr-x64 "$OUT/c0rt_natstr_x64.out" "$OUT/c0rt_natstr_x64.err" "$OUT/c0demo_ref.out"
check_run c0rt-natstr-arm64 "$OUT/c0rt_natstr_arm64.out" "$OUT/c0rt_natstr_arm64.err" "$OUT/c0demo_ref.out"

ref_prc="$(cat "$OUT/c0demo_ref_panic.rc")"
x64_prc="$(cat "$OUT/c0rt_natstr_x64_panic.rc")"
arm_prc="$(cat "$OUT/c0rt_natstr_arm64_panic.rc")"
if [ "$x64_prc" != "$ref_prc" ] || [ "$arm_prc" != "$ref_prc" ]; then
  echo "FAIL panic exit-code mismatch: ref=$ref_prc x64=$x64_prc arm64=$arm_prc" >&2
  exit 1
fi
echo "c0rt-panic: exit-code=$ref_prc parity OK (ref=x64=arm64)"

grep '^INTFUZZ' "$OUT/c0rt_int_x64.err"
grep -q '^LEAKCHECK ok' "$OUT/c0rt_int_x64.err"
grep -q '^LEAKCHECK ok' "$OUT/c0rt_int_arm64.err"
echo "c0rt-int-fuzz: x64 (ASan+UBSan) + arm64 QEMU LEAKCHECK ok"

echo "== test/lcnf/run_c0rt.sh: ALL CHECKS PASSED =="
