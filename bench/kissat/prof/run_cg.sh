#!/usr/bin/env bash
# Collect an uncompressed Callgrind profile for a single solver binary + CNF under timeout.
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: run_cg.sh [options] <binary> <cnf>

Options:
  --out PATH         Callgrind output path (default: <out-dir>/<bin>.<cnf_stem>.out)
  --out-dir DIR      Output directory when --out is omitted (default: /tmp/kissat_prof)
  --timeout SEC      Timeout in seconds (default: 900)
  --work BYTES       Solver workspace bytes (default: 67108864)
  --fuel TICKS       Solver tick fuel (default: 200000000)
  --flag TEL_FLAG    Telemetry flag (default: --full-telemetry-m2; pass "" to omit)
  --quiet            Suppress summary line
  -h, --help         Show this help
EOF
}

out=""
out_dir="/tmp/kissat_prof"
to="900"
work="67108864"
fuel="200000000"
tel_flag="--full-telemetry-m2"
quiet=0

while [[ $# -gt 0 ]]; do
  case "$1" in
    --out) out="$2"; shift 2 ;;
    --out-dir) out_dir="$2"; shift 2 ;;
    --timeout) to="$2"; shift 2 ;;
    --work) work="$2"; shift 2 ;;
    --fuel) fuel="$2"; shift 2 ;;
    --flag) tel_flag="$2"; shift 2 ;;
    --quiet) quiet=1; shift ;;
    -h|--help) usage; exit 0 ;;
    --) shift; break ;;
    -*) echo "Unknown option: $1" >&2; usage >&2; exit 2 ;;
    *) break ;;
  esac
done

if [[ $# -ne 2 ]]; then
  usage >&2
  exit 2
fi

bin="$1"
cnf="$2"

if [[ ! -x "$bin" ]]; then
  echo "error: binary is not executable: $bin" >&2
  exit 1
fi
if [[ ! -f "$cnf" ]]; then
  echo "error: CNF file not found: $cnf" >&2
  exit 1
fi
if ! command -v valgrind >/dev/null 2>&1; then
  echo "error: valgrind not found in PATH" >&2
  exit 1
fi

bname="$(basename "$bin")"
cname="$(basename "$cnf" .cnf)"
if [[ -z "$out" ]]; then
  out="$out_dir/$bname.$cname.out"
fi
mkdir -p "$(dirname "$out")"
prefix="${out%.out}"

cmd=("$bin")
if [[ -n "$tel_flag" ]]; then
  cmd+=("$tel_flag")
fi
cmd+=("$work" "$fuel" "$cnf")

set +e
timeout "$to" valgrind --tool=callgrind \
  --dump-instr=yes --compress-pos=no --compress-strings=no --collect-jumps=no \
  --callgrind-out-file="$out" \
  "${cmd[@]}" \
  > "$prefix.stdout" 2> "$prefix.stderr"
rc=$?
set -e

if [[ "$quiet" -eq 0 ]]; then
  echo "$bname $cname rc=$rc out=$out"
fi
exit "$rc"
