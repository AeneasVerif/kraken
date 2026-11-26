#!/usr/bin/env bash
# Resource-bounded Lake build runner with slice, memory, timeout, and thread caps.
#
# Usage:
#   scripts/build_bounded.sh [-j <jobs>] [-m <mem_max>] [-t <timeout_sec>]
#                            [--threads <N>] [--allow-broad] [--no-wfail]
#                            [--dry-run] [--] [<lake build targets...>]
#
# Defaults:
#   -j 1              Lake concurrency / worker thread limit (LEAN_NUM_THREADS=1)
#   -m 18G            systemd MemoryMax bound
#   -t 600            Execution timeout in seconds
#   --threads <N>     Alias for -j / --jobs (LEAN_NUM_THREADS)
#   --wfail           Fail on warnings (lake build --wfail ON by default)
#
# Broad Target Guard:
#   Unless --allow-broad is passed, bare umbrella targets (LeanQbe, LeanQbeAmd64,
#   LeanQbeArm64, LeanQbeTest, LeanQbeLegacy*, LeanQbeBootstrap0*) or target lists
#   lacking a concrete target are rejected to prevent accidental heavy builds.
#
set -euo pipefail

usage() {
  cat <<'EOF'
Usage: scripts/build_bounded.sh [OPTIONS] [--] [<lake build targets...>]

Options:
  -j, --jobs <N>       Lake build concurrency / thread cap (LEAN_NUM_THREADS, default: 1)
  --threads <N>        Alias for -j / --jobs (LEAN_NUM_THREADS)
  -m, --mem <SIZE>     systemd MemoryMax bound (default: 18G)
  -t, --timeout <SEC>  Timeout in seconds (default: 600)
  --allow-broad        Allow umbrella targets (LeanQbe, LeanQbeAmd64, LeanQbeArm64,
                       LeanQbeTest, LeanQbeLegacy*, LeanQbeBootstrap0*) or empty targets
  --no-wfail           Do not pass --wfail to lake build
  --wfail              Pass --wfail to lake build (default: enabled)
  --dry-run            Print the exact command and exit 0 without executing
  -h, --help           Show this help message and exit
EOF
}

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

JOBS="1"
MEM="18G"
TIMEOUT="600"
ALLOW_BROAD=0
WFAIL=1
DRY_RUN=0
TARGETS=()

while [ $# -gt 0 ]; do
  case "$1" in
    -j)
      [ $# -ge 2 ] && [ -n "$2" ] || { echo "build_bounded.sh: error: -j requires a non-empty argument" >&2; exit 2; }
      JOBS="$2"; shift 2 ;;
    -j*)
      val="${1#-j}"
      [ -n "$val" ] || { echo "build_bounded.sh: error: -j requires a non-empty argument" >&2; exit 2; }
      JOBS="$val"; shift ;;
    --jobs)
      [ $# -ge 2 ] && [ -n "$2" ] || { echo "build_bounded.sh: error: --jobs requires a non-empty argument" >&2; exit 2; }
      JOBS="$2"; shift 2 ;;
    --jobs=*)
      val="${1#--jobs=}"
      [ -n "$val" ] || { echo "build_bounded.sh: error: --jobs requires a non-empty argument" >&2; exit 2; }
      JOBS="$val"; shift ;;
    --threads)
      [ $# -ge 2 ] && [ -n "$2" ] || { echo "build_bounded.sh: error: --threads requires a non-empty argument" >&2; exit 2; }
      JOBS="$2"; shift 2 ;;
    --threads=*)
      val="${1#--threads=}"
      [ -n "$val" ] || { echo "build_bounded.sh: error: --threads requires a non-empty argument" >&2; exit 2; }
      JOBS="$val"; shift ;;
    -m)
      [ $# -ge 2 ] && [ -n "$2" ] || { echo "build_bounded.sh: error: -m requires a non-empty argument" >&2; exit 2; }
      MEM="$2"; shift 2 ;;
    -m*)
      val="${1#-m}"
      [ -n "$val" ] || { echo "build_bounded.sh: error: -m requires a non-empty argument" >&2; exit 2; }
      MEM="$val"; shift ;;
    --mem)
      [ $# -ge 2 ] && [ -n "$2" ] || { echo "build_bounded.sh: error: --mem requires a non-empty argument" >&2; exit 2; }
      MEM="$2"; shift 2 ;;
    --mem=*)
      val="${1#--mem=}"
      [ -n "$val" ] || { echo "build_bounded.sh: error: --mem requires a non-empty argument" >&2; exit 2; }
      MEM="$val"; shift ;;
    -t)
      [ $# -ge 2 ] && [ -n "$2" ] || { echo "build_bounded.sh: error: -t requires a non-empty argument" >&2; exit 2; }
      TIMEOUT="$2"; shift 2 ;;
    -t*)
      val="${1#-t}"
      [ -n "$val" ] || { echo "build_bounded.sh: error: -t requires a non-empty argument" >&2; exit 2; }
      TIMEOUT="$val"; shift ;;
    --timeout)
      [ $# -ge 2 ] && [ -n "$2" ] || { echo "build_bounded.sh: error: --timeout requires a non-empty argument" >&2; exit 2; }
      TIMEOUT="$2"; shift 2 ;;
    --timeout=*)
      val="${1#--timeout=}"
      [ -n "$val" ] || { echo "build_bounded.sh: error: --timeout requires a non-empty argument" >&2; exit 2; }
      TIMEOUT="$val"; shift ;;
    --allow-broad)
      ALLOW_BROAD=1; shift ;;
    --wfail)
      WFAIL=1; shift ;;
    --no-wfail)
      WFAIL=0; shift ;;
    --dry-run)
      DRY_RUN=1; shift ;;
    -h|--help)
      usage
      exit 0 ;;
    --)
      shift
      TARGETS+=("$@")
      break ;;
    -*)
      echo "build_bounded.sh: error: unknown option '$1'" >&2
      usage >&2
      exit 2 ;;
    *)
      TARGETS+=("$1")
      shift ;;
  esac
done

if [ "$ALLOW_BROAD" -eq 0 ]; then
  has_non_option=0
  for tgt in "${TARGETS[@]}"; do
    case "$tgt" in
      -*) ;;
      *) has_non_option=1 ;;
    esac
  done
  if [ "$has_non_option" -eq 0 ]; then
    echo "build_bounded.sh: error: no build targets specified. Bare builds default to all umbrella targets (including heavy Kissat builds). Specify explicit fine-grained targets (e.g. LeanQbeCore, LeanQbeAmd64Core, LeanQbeTest.T.Smoke) or pass --allow-broad to override." >&2
    exit 2
  fi
  for tgt in "${TARGETS[@]}"; do
    case "$tgt" in
      -*) continue ;;
    esac
    norm="$tgt"
    norm="${norm#@/}"
    norm="${norm#@}"
    norm="${norm#+}"
    norm="${norm%%:*}"
    case "$norm" in
      LeanQbe|LeanQbeAmd64|LeanQbeArm64|LeanQbeTest|LeanQbeLegacy*|LeanQbeBootstrap0*)
        echo "build_bounded.sh: error: broad umbrella target '$tgt' rejected. Use fine-grained targets (e.g. LeanQbeCore, LeanQbeAmd64Core, LeanQbeArm64Core, LeanQbeCoreTest, or a specific module) or pass --allow-broad to override." >&2
        exit 2
        ;;
    esac
  done
fi

WFAIL_ARGS=()
if [ "$WFAIL" -eq 1 ]; then
  WFAIL_ARGS=(--wfail)
fi

cmd=(
  timeout "$TIMEOUT"
  systemd-run --user --scope --quiet --slice=leanqbe-builds.slice
  -p "MemoryMax=$MEM"
  -p MemorySwapMax=0
  -p OOMPolicy=kill
  env
  LAKE_ARTIFACT_CACHE=true
  LAKE_RESTORE_ARTIFACTS=true
  "LEAN_NUM_THREADS=$JOBS"
  lake
  build
  "${WFAIL_ARGS[@]}"
  "${TARGETS[@]}"
)

if [ "$DRY_RUN" -eq 1 ]; then
  printf '%q' "${cmd[0]}"
  for ((i = 1; i < ${#cmd[@]}; i++)); do
    printf ' %q' "${cmd[i]}"
  done
  printf '\n'
  exit 0
fi

exec "${cmd[@]}"
