#!/usr/bin/env bash
# Common shared library and helper functions for bench/kissat/ benchmark and differential runners:
# (run_full.sh, run_plain.sh, run_4corner.sh, run.sh, build_solver.sh, test_cli_solver.sh).
#
# Provides:
#   - init_kissat_workspace: Root resolution, temp dir creation, cleanup trap handler
#   - run_lean_env: Timeout-guarded Lean 4 executor honoring STAGE_LEAN_PATH / LEAN_PATH
#   - resolve_kissat_oracle: Resolves upstream Kissat 4.0.4 reference binary or builds from scratch
#   - compile_c4_x64 / compile_c4_arm64: Standardized C-compiler wrappers with SFrame noise filtering
#   - run_arm64_qemu: AAPCS64 qemu-aarch64 execution helper
#   - query_solver_json: Centralized metadata queries against bench/kissat/solvers.json
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
RT_INC="$ROOT/LeanQbe/T/Runtime"
KTEST_INC="$ROOT/test/kissat"
SOLVERS_JSON="$ROOT/bench/kissat/solvers.json"

# Common compiler flag presets
COMMON_CXX_BASE="-std=c++20 -Wall -Wextra -Werror -I$RT_INC -I$KTEST_INC"
COMMON_C_BASE="-Wall -Wextra -Werror -I$KTEST_INC"

# Run lean script honoring STAGE_LEAN_PATH if exported
run_lean_env() {
  local secs="$1"; shift
  if [ -n "${STAGE_LEAN_PATH:-}" ]; then
    LEAN_PATH="$STAGE_LEAN_PATH:$ROOT/.lake/build/lib/lean${LEAN_PATH:+:$LEAN_PATH}" \
      timeout "$secs" lean "$@"
  else
    timeout "$secs" lake env lean "$@"
  fi
}

# Resolve or build reference Kissat binary
resolve_kissat_oracle() {
  local target_out="${1:-/tmp}"
  local resolved=""
  if [ -n "${KISSAT_BIN:-}" ]; then
    resolved="$KISSAT_BIN"
  elif [ -n "${KISSAT_REF_BIN:-}" ]; then
    resolved="$KISSAT_REF_BIN"
  elif [ -n "${KISSAT_SRC:-}" ] && [ -d "$KISSAT_SRC" ]; then
    mkdir -p "$target_out/kissat-src"
    cp -a "$KISSAT_SRC"/* "$target_out/kissat-src/"
    (
      cd "$target_out/kissat-src"
      rm -rf build makefile
      timeout 60 ./configure >/dev/null
      timeout 180 make -j"$(nproc)" >/dev/null
    )
    resolved="$target_out/kissat-src/build/kissat"
  elif [ -d "$ROOT/scratch/kissat/src" ]; then
    mkdir -p "$target_out/kissat-src"
    cp -a "$ROOT/scratch/kissat"/* "$target_out/kissat-src/"
    (
      cd "$target_out/kissat-src"
      rm -rf build makefile
      timeout 60 ./configure >/dev/null
      timeout 180 make -j"$(nproc)" >/dev/null
    )
    resolved="$target_out/kissat-src/build/kissat"
  else
    resolved="$(command -v kissat || true)"
  fi
  echo "$resolved"
}

# Compile native x64 assembly + harness
compile_c4_x64() {
  local opt_level="${1:-O2}"
  local c_src="$2"
  local s_src="$3"
  local out_bin="$4"
  local extra_flags=("${@:5}")
  local cc_bin="${CC:-gcc}"
  timeout 120 "$cc_bin" -std=c99 "-$opt_level" -Wall -Wextra -Werror -no-pie \
    -I"$KTEST_INC" "${extra_flags[@]}" "$c_src" "$s_src" -o "$out_bin"
}

# Compile native Arm64 assembly + harness with aarch64-linux-gnu-gcc
compile_c4_arm64() {
  local opt_level="${1:-O2}"
  local c_src="$2"
  local s_src="$3"
  local out_bin="$4"
  local log_file="${5:-/tmp/arm64_cc.log}"
  local extra_flags=("${@:6}")
  local cc_arm="${CC_AARCH64:-aarch64-linux-gnu-gcc}"
  timeout 120 "$cc_arm" -std=c99 "-$opt_level" -Wall -Wextra -Werror \
    -I"$KTEST_INC" "${extra_flags[@]}" "$c_src" "$s_src" -o "$out_bin" 2>"$log_file" || {
      cat "$log_file" >&2
      exit 1
    }
  grep -v -e 'SFrame' "$log_file" >&2 || true
}

# Run AAPCS64 binary under qemu-aarch64
run_arm64_qemu() {
  local secs="$1"; shift
  local bin="$1"; shift
  timeout "$secs" qemu-aarch64 -L /usr/aarch64-linux-gnu "$bin" "$@"
}

# Query metadata from solvers.json:
#   query_solver_json <module> <field>
query_solver_json() {
  local mod_name="$1"
  local field_name="$2"
  python3 -B - "$SOLVERS_JSON" "$mod_name" "$field_name" <<'PY'
import json, sys
data = json.load(open(sys.argv[1], "r", encoding="utf-8"))
req = sys.argv[2].strip().lower()
field = sys.argv[3]
matched = None
for k, v in data.items():
    if req == k.lower() or req in [a.lower() for a in v.get("aliases", [])]:
        matched = v
        break
if matched and field in matched:
    val = matched[field]
    if isinstance(val, list):
        print(" ".join(val))
    elif isinstance(val, bool):
        print("1" if val else "0")
    else:
        print(str(val))
else:
    sys.exit(1)
PY
}
