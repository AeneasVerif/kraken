#!/usr/bin/env bash
# Phase 1: Apples-to-apples 4-Corner (C1/C2/C3b/C4) performance isolation harness.
#
# Builds & benchmarks `Full` and/or `FullFast` across:
#   - C3b: `PrintCpp` -> `clang++ -std=c++20 -O3 -DTQBE_NATIVE_MEM` linked with `bench_main.c`
#   - C4 : `lean-qbe` native x64 `.s` -> `clang -O3 -no-pie` linked with `bench_main.c`
#   - Optional C1: upstream Kissat 4.0.4 (`--kissat <bin>`) if available
#
# Asserts BIT-IDENTICAL `(status, conflicts, learned_lits, min_removed, search_ticks)`
# between C3b and C4, separating `C0 -> T` lowering from `lean-qbe` backend codegen.
#
# Environment knobs:
#   STAGE_LEAN_PATH - Optional read-only prebuilt `.lake/build/lib/lean` path (avoids rebuild)
#   WORK_BYTES      - Workspace bytes (default: 67108864 = 64 MiB)
#   FUEL            - Solver fuel budget (default: 200000000)
#   PER_TIMEOUT     - Per-CNF timeout seconds (default: 5)
#   WITH_PERF       - Set to 1 to collect `perf stat` counters on representative canaries
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

MODULES=(Full FullFast FullM3)
WORK_BYTES="${WORK_BYTES:-67108864}"
FUEL="${FUEL:-200000000}"
PER_TIMEOUT="${PER_TIMEOUT:-5}"
WITH_PERF="${WITH_PERF:-0}"
KISSAT_BIN="${KISSAT_BIN:-}"
UPDATE_BASELINE=0
STRICT_GAPS=0
FILTER=""

usage() {
  cat <<'EOF'
usage: bench/kissat/run_4corner.sh [options]
  --module <Full|FullFast|FullM3|Both|All>  Module(s) to benchmark (default: All)
  --kissat <bin>                            Optional upstream Kissat 4.0.4 binary (C1)
  --work-bytes <N>                          Workspace bytes (default: 67108864)
  --fuel <N>                                Fuel budget (default: 200000000)
  --per-timeout <sec>                       Per-CNF timeout seconds (default: 5)
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
        full) MODULES=(Full) ;;
        fullfast) MODULES=(FullFast) ;;
        fullm3|m3) MODULES=(FullM3) ;;
        both) MODULES=(Full FullFast) ;;
        all) MODULES=(Full FullFast FullM3) ;;
        *) echo "ERROR: unknown module '$2'" >&2; exit 2 ;;
      esac
      shift 2
      ;;
    --kissat) KISSAT_BIN="$2"; shift 2 ;;
    --work-bytes) WORK_BYTES="$2"; shift 2 ;;
    --fuel) FUEL="$2"; shift 2 ;;
    --per-timeout) PER_TIMEOUT="$2"; shift 2 ;;
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
    LEAN_PATH="$STAGE_LEAN_PATH" timeout 300 lean --run "$@"
  else
    timeout 300 lake env lean --run "$@"
  fi
}

if [ -z "${STAGE_LEAN_PATH:-}" ]; then
  LAKE_TARGETS=(
    LeanQbe.T.PrintCpp LeanQbe.T.Driver
    LeanQbe.T.Amd64.Targ Kraken.X64.PrintATT
  )
  for m in "${MODULES[@]}"; do
    LAKE_TARGETS+=("LeanQbe.T.Examples.Kissat.$m")
  done
  echo "== 2. lake build ${LAKE_TARGETS[*]} =="
  timeout 600 lake build --wfail "${LAKE_TARGETS[@]}"
else
  echo "== 2. Using prebuilt STAGE_LEAN_PATH=$STAGE_LEAN_PATH (0 lake build) =="
fi

mod_expr() {
  case "$1" in
    Full) echo "LeanQbe.T.Examples.Kissat.Full.fullModule" ;;
    FullFast) echo "LeanQbe.T.Examples.Kissat.FullFast.fastModule" ;;
    FullM3) echo "LeanQbe.T.Examples.Kissat.FullM3.m3Module" ;;
  esac
}

CC="${CC:-clang}"
CXX="${CXX:-clang++}"
KTEST_INC="$ROOT/test/kissat"
RT_INC="$ROOT/LeanQbe/T/Runtime"

CHECK_ARGS=(--cnf-dir "$OUT/cnfs" --work-bytes "$WORK_BYTES" --fuel "$FUEL" --per-timeout "$PER_TIMEOUT")
[ -n "$KISSAT_BIN" ] && CHECK_ARGS+=(--kissat "$KISSAT_BIN")
[ "$UPDATE_BASELINE" -eq 1 ] && CHECK_ARGS+=(--update-baseline --commit "$(git rev-parse HEAD)")
[ "$STRICT_GAPS" -eq 1 ] && CHECK_ARGS+=(--strict-gaps)
[ -n "$FILTER" ] && CHECK_ARGS+=(--filter "$FILTER")

for m in "${MODULES[@]}"; do
  expr="$(mod_expr "$m")"
  echo "== 3[$m]. Emit PrintCpp (.hpp) + native x64 (.s) =="
  cat > "$OUT/emit_${m}.lean" <<LEAN
import LeanQbe.T.Examples.Kissat.${m}
import LeanQbe.T.PrintCpp
import LeanQbe.T.Driver
import LeanQbe.T.Amd64.Targ
import Kraken.X64.PrintATT

open LeanQbe.T LeanQbe.T.PrintCpp LeanQbe.T.Amd64

public def main (args : List String) : IO Unit := do
  let [cppPath, x64Path] := args | throw (IO.userError "usage: <cpp> <x64>")
  let m := ${expr}
  let cpp ← match ppTModule m with
    | .ok s => pure s
    | .error e => throw (IO.userError e)
  IO.FS.writeFile cppPath cpp
  let fns := m.fns
  let hints := fns.map (Fn.computeHints x64Target.toIsa x64LegalTarget)
  let dirs ← match LeanQbe.T.compile x64Target.toIsa x64LegalTarget fns hints with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  IO.FS.writeFile x64Path (Driver.emitAsm (fun c => Kraken.X64.toATT c ++ "\n") fns dirs)
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
    Full) CHECK_ARGS+=(--full-c4 "$OUT/c4_Full" --full-c3b "$OUT/c3b_Full") ;;
    FullFast) CHECK_ARGS+=(--fast-c4 "$OUT/c4_FullFast" --fast-c3b "$OUT/c3b_FullFast") ;;
    FullM3) CHECK_ARGS+=(--m3-c4 "$OUT/c4_FullM3" --m3-c3b "$OUT/c3b_FullM3") ;;
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
