#!/usr/bin/env bash
# Direct C0 -> C99 -> clang -std=c99 -O3 builder (zero Lean/QBE/PrintCpp/clang++).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
if [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean" ]; then
  TARGET="fidelity"
elif [ -f "$ROOT/LeanQbe/T/Examples/Kissat/FullM7FidelityAssembly.lean" ]; then
  TARGET="m7fidelity"
else
  TARGET="m5"
fi
OUT_DIR="/tmp/kissat-c0direct"
OUT_BIN=""
ASAN=0
CHECK_FNS=""

usage() {
  cat <<'EOF'
usage: bash bench/kissat/build_c0_direct.sh [options]
  --target <fidelity|m8opt|plain|m7fidelity|m7plus|m7|m6|m5>
                         Kissat C0 splice target (aliases: fid, opt, m8; default: auto fidelity/m7fidelity)
  --out-dir <dir>        Output directory for .c/.o/binary (default: /tmp/kissat-c0direct)
  -o, --out <bin>        Explicit output binary path (default: <out-dir>/bench_c0direct_<target>[_asan])
  --asan                 Enable -fsanitize=undefined,address -fno-sanitize-recover=all
  --check-fns <arg>      Optional parity check forwarded to extract_c0_direct.py
  -h, --help             Show this help
EOF
}

while [ $# -gt 0 ]; do
  case "$1" in
    --target) TARGET="$2"; shift 2 ;;
    --out-dir) OUT_DIR="$2"; shift 2 ;;
    -o|--out) OUT_BIN="$2"; shift 2 ;;
    --asan) ASAN=1; shift ;;
    --check-fns) CHECK_FNS="$2"; shift 2 ;;
    -h|--help) usage; exit 0 ;;
    *) echo "ERROR: unknown argument '$1'" >&2; usage >&2; exit 2 ;;
  esac
done

case "$TARGET" in
  plain|fidelity|fid|m8opt|opt|m8|m5|m6|m7|m7plus|m7fidelity|m7plus-memshrink|m7fidelity-memshrink) ;;
  *) echo "ERROR: unsupported --target '$TARGET'" >&2; exit 2 ;;
esac

mkdir -p "$OUT_DIR"
SUFFIX=""
SAN_FLAGS=()
if [ "$ASAN" -eq 1 ]; then
  SUFFIX="_asan"
  SAN_FLAGS=(-fsanitize=undefined,address -fno-sanitize-recover=all)
fi
OUT_BIN="${OUT_BIN:-$OUT_DIR/bench_c0direct_${TARGET}${SUFFIX}}"
C_SRC="$OUT_DIR/${TARGET}_direct.c"
C_OBJ="$OUT_DIR/${TARGET}_direct${SUFFIX}.o"
MAIN_OBJ="$OUT_DIR/bench_main${SUFFIX}.o"

EXT_ARGS=(--target "$TARGET" --out "$C_SRC")
[ -n "$CHECK_FNS" ] && EXT_ARGS+=(--check-fns "$CHECK_FNS")

t0_ns="$(date +%s%N)"
timeout 30 python3 -B "$ROOT/bench/kissat/extract_c0_direct.py" "${EXT_ARGS[@]}"
t1_ns="$(date +%s%N)"

CC="${CC:-clang}"
C0_FLAGS=(-std=c99 -O3 -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror)
# Plain's C0 has one unparenthesized `a || b && c` (clang -Wlogical-op-parentheses,
# gcc -Wparentheses); fidelity/opt targets stay warning-free without it.
if [ "$TARGET" = plain ]; then C0_FLAGS+=(-Wno-parentheses); fi
MAIN_FLAGS=(-std=c99 -O3 -Wall -Wextra -Werror)

timeout 60 "$CC" "${C0_FLAGS[@]}" "${SAN_FLAGS[@]}" \
  -I"$ROOT/LeanQbe/T/Frontend/C0" -c "$C_SRC" -o "$C_OBJ"
t2_ns="$(date +%s%N)"

timeout 60 "$CC" "${MAIN_FLAGS[@]}" "${SAN_FLAGS[@]}" \
  -I"$ROOT/test/kissat" -c "$ROOT/bench/kissat/bench_main.c" -o "$MAIN_OBJ"
timeout 60 "$CC" "${SAN_FLAGS[@]}" "$C_OBJ" "$MAIN_OBJ" -o "$OUT_BIN"
t3_ns="$(date +%s%N)"

awk -v t0="$t0_ns" -v t1="$t1_ns" -v t2="$t2_ns" -v t3="$t3_ns" -v bin="$OUT_BIN" \
  'BEGIN { printf "Built %s (extract=%.0fms compile=%.0fms link+main=%.0fms total=%.0fms)\n",
             bin, (t1-t0)/1e6, (t2-t1)/1e6, (t3-t2)/1e6, (t3-t0)/1e6 }'
