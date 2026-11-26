#!/usr/bin/env bash
# 4-Corner (C1/C2/C3b/C4) performance isolation harness for Kissat modules.
#
# Builds & benchmarks `Full` and/or `FullFast` across:
#   - C3b: `PrintCpp` -> `clang++ -std=c++20 -O3 -DTQBE_NATIVE_MEM` linked with `bench_main.c`
#   - C4 : `lean-qbe` native x64 `.s` -> `clang -O3 -no-pie` linked with `bench_main.c`
#   - Optional C1: upstream Kissat 4.0.4 (`--kissat <bin>`, `KISSAT_BIN`, or `kissat` in `PATH`)
#
# Asserts BIT-IDENTICAL `(status, conflicts, learned_lits, min_removed, search_ticks)`
# between C3b and C4, separating `C0 -> T` lowering from `lean-qbe` backend codegen.
#
# Environment knobs:
#   STAGE_LEAN_PATH - Optional read-only prebuilt `.lake/build/lib/lean` path (avoids rebuild)
#   KISSAT_BIN      - Optional upstream Kissat 4.0.4 binary (auto-detected via PATH if unset)
#   WORK_BYTES      - Workspace bytes (default: 67108864 = 64 MiB)
#   FUEL            - Solver fuel budget (default: 200000000)
#   PER_TIMEOUT     - Per-CNF timeout seconds (default: 5)
#   WITH_PERF       - Set to 1 to collect `perf stat` counters on representative canaries
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

if [ -f "$ROOT/LeanQbe/T/Amd64/KissatFidelity.lean" ] && \
   [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean" ]; then
  MODULES=(KissatFidelity)
elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean" ]; then
  MODULES=(FullM7Fidelity)
else
  MODULES=(Full FullFast FullM3 FullM4)
fi
WORK_BYTES="${WORK_BYTES:-67108864}"
FUEL="${FUEL:-200000000}"
PER_TIMEOUT="${PER_TIMEOUT:-5}"
WITH_PERF="${WITH_PERF:-0}"
KISSAT_BIN="${KISSAT_BIN:-}"
NO_KISSAT=0
C2_FLAGS=""
C2_PRESET=""
INLINE_MAX_SIZE="${INLINE_MAX_SIZE:-}"
UPDATE_BASELINE=0
STRICT_GAPS=0
FILTER=""

usage() {
  cat <<'EOF'
usage: bench/kissat/run_4corner.sh [options]
  --module <KissatFidelity|KissatM8Opt|Plain|FullM7Fidelity|Full|FullFast|FullM3|FullM4|Both|All>
                                            Module(s) to benchmark (default: auto KissatFidelity/FullM7Fidelity)
  --kissat <bin>                            Optional upstream Kissat 4.0.4 binary (C1)
  --no-kissat                               Disable C1 even if kissat is in PATH/KISSAT_BIN
  --c2-flags "<flags>"                      Flag-matched Kissat 4.0.4 corner (C2)
  --c2-preset <plain|m4|m5|fidelity|m8opt>  Preset flags for C2 corner
  --work-bytes <N>                          Workspace bytes (default: 67108864)
  --fuel <N>                                Fuel budget (default: 200000000)
  --per-timeout <sec>                       Per-CNF timeout seconds (default: 5)
  --inline-max <N>                          Module.optInline maxSize for C4 (default: 0 for Fidelity/Opt/Plain, 40 for legacy)
  --perf                                    Run perf stat hardware counter comparison (C3b vs C4)
  --update-baseline                         Update bench/kissat/canary_baseline.json
  --strict-gaps                             Fail on known pre-M3 gaps too
  --filter <substr>                         Filter canaries by filename substring
  -h, --help                                Show help
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --module)
      case "${2,,}" in
        kissatfidelity|fullfidelity|fidelity|fid) MODULES=(KissatFidelity) ;;
        kissatm8opt|fullm8opt|m8opt|opt|fullm8|m8) MODULES=(KissatM8Opt) ;;
        plain|kissatplain) MODULES=(Plain) ;;
        fullm7fidelity|m7fidelity|m7fid) MODULES=(FullM7Fidelity) ;;
        full) MODULES=(Full) ;;
        fullfast) MODULES=(FullFast) ;;
        fullm3|m3) MODULES=(FullM3) ;;
        fullm4|m4) MODULES=(FullM4) ;;
        both) MODULES=(Full FullFast) ;;
        all)
          MODULES=()
          [ -f "$ROOT/LeanQbe/T/Examples/Kissat/Plain.lean" ] && MODULES+=(Plain)
          if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean" ]; then
            MODULES+=(KissatFidelity)
          elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean" ]; then
            MODULES+=(FullM7Fidelity)
          fi
          [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8OptAssembly.lean" ] && MODULES+=(KissatM8Opt)
          ;;
        *) echo "ERROR: unknown module '$2'" >&2; exit 2 ;;
      esac
      shift 2
      ;;
    --kissat)
      [ $# -ge 2 ] || { echo "ERROR: --kissat requires an argument" >&2; exit 2; }
      KISSAT_BIN="$2"; shift 2 ;;
    --no-kissat) NO_KISSAT=1; KISSAT_BIN=""; shift ;;
    --c2-flags)
      [ $# -ge 2 ] || { echo "ERROR: --c2-flags requires an argument" >&2; exit 2; }
      C2_FLAGS="$2"; shift 2 ;;
    --c2-preset)
      [ $# -ge 2 ] || { echo "ERROR: --c2-preset requires an argument" >&2; exit 2; }
      C2_PRESET="${2,,}"; shift 2 ;;
    --work-bytes) WORK_BYTES="$2"; shift 2 ;;
    --fuel) FUEL="$2"; shift 2 ;;
    --per-timeout) PER_TIMEOUT="$2"; shift 2 ;;
    --inline-max) INLINE_MAX_SIZE="$2"; shift 2 ;;
    --perf) WITH_PERF=1; shift ;;
    --update-baseline) UPDATE_BASELINE=1; shift ;;
    --strict-gaps) STRICT_GAPS=1; shift ;;
    --filter) FILTER="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "ERROR: unknown option '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-4corner.XXXXXX")}"
cleanup() {
  if [ -z "$OUT_USER" ] && [ -z "${KEEP_OUT:-}" ]; then
    rm -rf "$OUT"
  fi
}
trap cleanup EXIT
mkdir -p "$OUT/cnfs"
echo "outputs in $OUT (modules: ${MODULES[*]}, work=${WORK_BYTES}B, timeout=${PER_TIMEOUT}s)"

echo "== 1. Generate 10-family tricky-UNSAT canary suite =="
timeout 60 python3 -B bench/kissat/gen_canary_cnfs.py "$OUT/cnfs" --summary

run_lean_env() {
  if [ -n "${STAGE_LEAN_PATH:-}" ]; then
    LEAN_PATH="$STAGE_LEAN_PATH" timeout 900 lean --run "$@"
  else
    timeout 900 lake env lean --run "$@"
  fi
}

mod_lean() {
  case "$1" in
    KissatFidelity)
      local deps=("LeanQbe.T.Examples.Kissat.FullFidelityAssembly")
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityInlPolicy.lean" ]; then
        deps+=("LeanQbe.T.MainInline" "LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy")
      fi
      echo "${deps[*]}" ;;
    KissatM8Opt)
      local deps=("LeanQbe.T.Examples.Kissat.FullM8OptAssembly")
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8InlPolicy.lean" ]; then
        deps+=("LeanQbe.T.MainInline" "LeanQbe.T.Examples.Kissat.FullM8InlPolicy")
      fi
      echo "${deps[*]}" ;;
    FullM7Fidelity)
      local deps=("LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly")
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean" ]; then
        deps+=("LeanQbe.T.MainInline" "LeanQbe.T.Examples.Kissat.FullM7InlPolicy")
      fi
      echo "${deps[*]}" ;;
    Plain|Full|FullFast|FullM3|FullM4)
      echo "LeanQbe.T.Examples.Kissat.$1" ;;
  esac
}

if [ -z "${STAGE_LEAN_PATH:-}" ]; then
  LAKE_TARGETS=(
    LeanQbe.T.PrintCpp LeanQbe.T.Opt LeanQbe.T.Driver
    LeanQbe.T.Amd64.Targ LeanQbe.T.Amd64.PrintATTAlign
  )
  for m in "${MODULES[@]}"; do
    # shellcheck disable=SC2046
    LAKE_TARGETS+=($(mod_lean "$m"))
  done
  echo "== 2. lake build ${LAKE_TARGETS[*]} =="
  timeout 600 lake build --wfail "${LAKE_TARGETS[@]}"
else
  echo "== 2. Using prebuilt STAGE_LEAN_PATH=$STAGE_LEAN_PATH (0 lake build) =="
fi

mod_expr() {
  case "$1" in
    KissatFidelity) echo "LeanQbe.T.Examples.Kissat.FullFidelityAssembly.fidModule" ;;
    KissatM8Opt) echo "LeanQbe.T.Examples.Kissat.FullM8OptAssembly.m8OptModule" ;;
    FullM7Fidelity) echo "LeanQbe.T.Examples.Kissat.FullM7Fidelity.m7FidelityModule" ;;
    Plain) echo "LeanQbe.T.Examples.Kissat.Plain.plainModule" ;;
    Full) echo "LeanQbe.T.Examples.Kissat.Full.fullModule" ;;
    FullFast) echo "LeanQbe.T.Examples.Kissat.FullFast.fastModule" ;;
    FullM3) echo "LeanQbe.T.Examples.Kissat.FullM3.m3Module" ;;
    FullM4) echo "LeanQbe.T.Examples.Kissat.FullM4.m4Module" ;;
  esac
}

mod_inl_fns() {
  case "$1" in
    KissatFidelity)
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityInlPolicy.lean" ]; then
        echo "(m.optInlinePolicy LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy.fidInlPolicy).fns"
      else
        echo "m.fns"
      fi ;;
    KissatM8Opt)
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM8InlPolicy.lean" ]; then
        echo "(m.optInlinePolicy LeanQbe.T.Examples.Kissat.FullM8InlPolicy.m8InlPolicy).fns"
      else
        echo "m.fns"
      fi ;;
    FullM7Fidelity)
      if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7InlPolicy.lean" ]; then
        echo "(m.optInlinePolicy LeanQbe.T.Examples.Kissat.FullM7InlPolicy.m7InlPolicy).fns"
      else
        echo "m.fns"
      fi ;;
    Plain) echo "m.fns" ;;
    *) echo "(m.optInline 40).fns" ;;
  esac
}

CC="${CC:-clang}"
CXX="${CXX:-clang++}"
KTEST_INC="$ROOT/test/kissat"
RT_INC="$ROOT/LeanQbe/T/Runtime"

if [ "$NO_KISSAT" -eq 0 ] && [ -z "$KISSAT_BIN" ]; then
  SYS_KISSAT="$(command -v kissat 2>/dev/null || true)"
  if [ -n "$SYS_KISSAT" ] && [ -x "$SYS_KISSAT" ]; then
    KISSAT_BIN="$SYS_KISSAT"
  fi
fi
if [ -n "$KISSAT_BIN" ]; then
  RESOLVED_KISSAT="$(command -v "$KISSAT_BIN" 2>/dev/null || true)"
  if [ -z "$RESOLVED_KISSAT" ] || [ ! -x "$RESOLVED_KISSAT" ]; then
    echo "ERROR: kissat binary '$KISSAT_BIN' not found or not executable" >&2
    exit 2
  fi
  KISSAT_BIN="$RESOLVED_KISSAT"
  echo "C1 oracle: $KISSAT_BIN"
fi

if [ -n "$C2_PRESET" ] && [ -z "$C2_FLAGS" ]; then
  case "$C2_PRESET" in
    plain)
      C2_FLAGS="--plain --seed=0 --phase=1 --tumble=0 --reorder=0 --stable=1 --rephase=1 --target=1" ;;
    m4)
      C2_FLAGS="--seed=0 --phase=1 --jumpreasons=0 --randec=0 --vivifysort=0 --eliminatebound=8 --eliminateocclim=64 --congruencexorarity=2 --sweepvars=128 --sweepmaxvars=128 --factorsize=5" ;;
    m5|fidelity|m8opt|m8)
      C2_FLAGS="--seed=0 --phase=1 --jumpreasons=0 --randec=0" ;;
    *)
      echo "ERROR: unknown --c2-preset '$C2_PRESET' (expected plain|m4|m5|fidelity|m8opt)" >&2
      exit 2 ;;
  esac
fi

CHECK_ARGS=(--cnf-dir "$OUT/cnfs" --work-bytes "$WORK_BYTES" --fuel "$FUEL" --per-timeout "$PER_TIMEOUT")
[ -n "$KISSAT_BIN" ] && CHECK_ARGS+=(--kissat "$KISSAT_BIN")
[ -n "$C2_FLAGS" ] && CHECK_ARGS+=(--c2-flags "$C2_FLAGS")
[ "$UPDATE_BASELINE" -eq 1 ] && CHECK_ARGS+=(--update-baseline --commit "$(git rev-parse HEAD)")
[ "$STRICT_GAPS" -eq 1 ] && CHECK_ARGS+=(--strict-gaps)
[ -n "$FILTER" ] && CHECK_ARGS+=(--filter "$FILTER")

for m in "${MODULES[@]}"; do
  expr="$(mod_expr "$m")"
  if [ -n "$INLINE_MAX_SIZE" ] && [ "$INLINE_MAX_SIZE" -gt 0 ]; then
    fns_expr="(m.optInline ${INLINE_MAX_SIZE}).fns"
  elif [ -n "$INLINE_MAX_SIZE" ] && [ "$INLINE_MAX_SIZE" -eq 0 ]; then
    case "$m" in
      Full|FullFast|FullM3|FullM4) fns_expr="m.fns" ;;
      *) fns_expr="$(mod_inl_fns "$m")" ;;
    esac
  else
    fns_expr="$(mod_inl_fns "$m")"
  fi
  imports=""
  for lm in $(mod_lean "$m"); do
    imports+="import $lm"$'\n'
  done
  echo "== 3[$m]. Emit PrintCpp (.hpp) + native x64 (.s) =="
  cat > "$OUT/emit_${m}.lean" <<LEAN
${imports}import LeanQbe.T.PrintCpp
import LeanQbe.T.Opt
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import LeanQbe.T.Amd64.PrintATTAlign

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let [cppPath, x64Path] := args | throw (IO.userError "usage: <cpp> <x64>")
  let m := ${expr}
  let cpp ← match ppTModule m with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  IO.FS.writeFile cppPath cpp
  let fns := ${fns_expr}
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  IO.FS.writeFile x64Path (Driver.emitAsm (fun c => toATTAligned c ++ "\n") fns dirs)
LEAN
  run_lean_env "$OUT/emit_${m}.lean" "$OUT/${m}_gen.hpp" "$OUT/${m}_x64.s"

  echo "== 4[$m]. Compile C4 (native x64) + C3b (PrintCpp -DTQBE_NATIVE_MEM) with $CC/$CXX -O3 =="
  timeout 120 "$CC" -std=c99 -O3 -Wall -Wextra -Werror -no-pie -I"$KTEST_INC" \
    bench/kissat/bench_main.c "$OUT/${m}_x64.s" -o "$OUT/c4_${m}"

  cat > "$OUT/c3b_${m}_bridge.cpp" <<CPP
#include <cstdint>
#include "tqbe_rt.hpp"

namespace tqbe_gen {
#include "${m}_gen.hpp"
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
  timeout 120 "$CC" -std=c99 -O3 -Wall -Wextra -Werror -I"$KTEST_INC" \
    -c bench/kissat/bench_main.c -o "$OUT/bench_main.o"
  timeout 300 "$CXX" -std=c++20 -O3 -Wall -Wextra -Werror -DTQBE_NATIVE_MEM \
    -I"$RT_INC" -I"$OUT" "$OUT/c3b_${m}_bridge.cpp" "$OUT/bench_main.o" -o "$OUT/c3b_${m}"

  case "$m" in
    Plain) CHECK_ARGS+=(--plain-c4 "$OUT/c4_Plain" --plain-c3b "$OUT/c3b_Plain") ;;
    KissatFidelity) CHECK_ARGS+=(--fid-c4 "$OUT/c4_KissatFidelity" --fid-c3b "$OUT/c3b_KissatFidelity") ;;
    FullM7Fidelity) CHECK_ARGS+=(--m7fid-c4 "$OUT/c4_FullM7Fidelity" --m7fid-c3b "$OUT/c3b_FullM7Fidelity") ;;
    KissatM8Opt) CHECK_ARGS+=(--opt-c4 "$OUT/c4_KissatM8Opt" --opt-c3b "$OUT/c3b_KissatM8Opt") ;;
    Full) CHECK_ARGS+=(--full-c4 "$OUT/c4_Full" --full-c3b "$OUT/c3b_Full") ;;
    FullFast) CHECK_ARGS+=(--fast-c4 "$OUT/c4_FullFast" --fast-c3b "$OUT/c3b_FullFast") ;;
    FullM3) CHECK_ARGS+=(--m3-c4 "$OUT/c4_FullM3" --m3-c3b "$OUT/c3b_FullM3") ;;
    FullM4) CHECK_ARGS+=(--m4-c4 "$OUT/c4_FullM4" --m4-c3b "$OUT/c3b_FullM4") ;;
  esac
done

echo "== 5. Run 10-family canary check & C4 == C3b parity verification =="
timeout 600 python3 -B bench/kissat/check_canaries.py "${CHECK_ARGS[@]}"

if [ "$WITH_PERF" -eq 1 ] && command -v perf >/dev/null 2>&1; then
  echo "== 6. Hardware counter comparison (perf stat: C3b vs C4) =="
  PERF_CNF="$OUT/cnfs/c08_ordering_8.cnf"
  [ -f "$PERF_CNF" ] || PERF_CNF="$(ls "$OUT"/cnfs/*.cnf | head -1)"
  for m in "${MODULES[@]}"; do
    for corner in c3b c4; do
      echo "--- perf stat ${corner}_${m} on $(basename "$PERF_CNF") ---"
      timeout 30 perf stat -e cycles,instructions,branches,branch-misses,L1-dcache-loads,L1-dcache-load-misses \
        -- "$OUT/${corner}_${m}" --full-telemetry "$WORK_BYTES" "$FUEL" "$PERF_CNF" >/dev/null 2>&1 || \
        echo "(perf stat unavailable or restricted by perf_event_paranoid)"
    done
  done
fi

echo "== bench/kissat/run_4corner.sh: COMPLETE =="
