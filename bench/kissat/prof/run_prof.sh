#!/usr/bin/env bash
# Profile LeanQbe x64 (C4) vs PrintCpp C++20 (C3b) under Callgrind and compare per-class/per-fn Ir.
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

usage() {
  cat <<'EOF'
Usage: run_prof.sh --c4 <c4_bin> --c3b <c3b_bin> [options] <cnf>...

Collects Callgrind dynamic instruction counts (under timeout) for C4 and C3b
on each CNF and prints per-instruction-class and per-function C4 vs C3b reports.

Options:
  --c4 PATH          Path to C4 binary (required)
  --c3b PATH         Path to C3b binary (required)
  --out-dir DIR      Directory for .out/.stdout/.stderr files (default: /tmp/kissat_prof)
  --timeout SEC      Per-run Valgrind timeout in seconds (default: 900)
  --work BYTES       Solver workspace bytes (default: 67108864)
  --fuel TICKS       Solver tick fuel (default: 200000000)
  --flag TEL_FLAG    Telemetry flag (default: --full-telemetry-m2)
  --top N            Top N functions per CNF report (default: 14)
  --skip-existing    Reuse existing .out files in --out-dir when non-empty
  -h, --help         Show this help
EOF
}

c4=""
c3b=""
out_dir="/tmp/kissat_prof"
to="900"
work="67108864"
fuel="200000000"
tel_flag="--full-telemetry-m2"
top="14"
skip_existing=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --c4) c4="$2"; shift 2 ;;
    --c3b) c3b="$2"; shift 2 ;;
    --out-dir) out_dir="$2"; shift 2 ;;
    --timeout) to="$2"; shift 2 ;;
    --work) work="$2"; shift 2 ;;
    --fuel) fuel="$2"; shift 2 ;;
    --flag) tel_flag="$2"; shift 2 ;;
    --top) top="$2"; shift 2 ;;
    --skip-existing) skip_existing=1; shift ;;
    -h|--help) usage; exit 0 ;;
    --) shift; break ;;
    -*) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    *) break ;;
  esac
done

if [[ -z "$c4" || -z "$c3b" || $# -lt 1 ]]; then
  usage >&2
  exit 2
fi
if ! command -v objdump >/dev/null 2>&1; then
  echo "error: objdump not found in PATH" >&2
  exit 1
fi

mkdir -p "$out_dir"
b4="$(basename "$c4")"
b3="$(basename "$c3b")"

for cnf in "$@"; do
  cname="$(basename "$cnf" .cnf)"
  for spec in "c4:$c4:$b4" "c3b:$c3b:$b3"; do
    IFS=: read -r role bin bname <<< "$spec"
    out="$out_dir/$bname.$cname.out"
    if [[ "$skip_existing" -eq 1 && -s "$out" ]]; then
      echo "reusing $out" >&2
      continue
    fi
    "$SCRIPT_DIR/run_cg.sh" \
      --out "$out" --timeout "$to" --work "$work" --fuel "$fuel" --flag "$tel_flag" \
      "$bin" "$cnf"
  done
done

timeout "$to" python3 -B "$SCRIPT_DIR/summary.py" \
  --c4 "$c4" --c3b "$c3b" --cg-dir "$out_dir" --top "$top" "$@"
