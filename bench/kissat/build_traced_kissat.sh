#!/usr/bin/env bash
# Build an opt-in traced Kissat 4.0.4 binary (`-DKISSAT_LOCKSTEP_TRACE`) in a
# temporary/scratch directory without mutating the reference Kissat tree or repo.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PATCH_FILE="$ROOT/bench/kissat/kissat_lockstep_trace.patch"
DEFAULT_SRC="/usr/local/google/home/andreser/.gemini/jetski/brain/f0cea481-7468-44ed-8bb8-8bc2c8436b38/scratch/kissat-ref-clang"

SRC_DIR="${1:-$DEFAULT_SRC}"
OUT_BIN="${2:-/usr/local/google/home/andreser/.gemini/jetski/brain/f0cea481-7468-44ed-8bb8-8bc2c8436b38/scratch/fidelity_lockstep/kissat-traced}"
CC="${CC:-clang}"

if [ ! -d "$SRC_DIR/src" ]; then
  echo "ERROR: Kissat source directory not found: $SRC_DIR" >&2
  exit 2
fi
if [ ! -f "$PATCH_FILE" ]; then
  echo "ERROR: patch not found: $PATCH_FILE" >&2
  exit 2
fi

TMP_BUILD="$(mktemp -d "${TMPDIR:-/tmp}/kissat-traced-build.XXXXXX")"
trap 'rm -rf "$TMP_BUILD"' EXIT

cp -a "$SRC_DIR/." "$TMP_BUILD/kissat/"
cd "$TMP_BUILD/kissat"
rm -rf build makefile src/makefile
patch -p1 --batch < "$PATCH_FILE"
CC="$CC" CFLAGS="-DKISSAT_LOCKSTEP_TRACE" timeout 60 ./configure --compact >/dev/null
# Ensure -DKISSAT_LOCKSTEP_TRACE is on CC line in build/makefile
sed -i 's/^CC=\(.*\)$/CC=\1 -DKISSAT_LOCKSTEP_TRACE/' build/makefile
timeout 180 make -j"$(nproc)" kissat >/dev/null

mkdir -p "$(dirname "$OUT_BIN")"
cp -f build/kissat "$OUT_BIN"
chmod +x "$OUT_BIN"
echo "Built traced Kissat: $OUT_BIN"
