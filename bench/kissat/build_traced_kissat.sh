#!/usr/bin/env bash
# Build an opt-in traced Kissat 4.0.4 binary (`-DKISSAT_LOCKSTEP_TRACE`) in a
# temporary/scratch directory without mutating the reference Kissat tree or repo.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
PATCH_FILE="$ROOT/bench/kissat/kissat_lockstep_trace.patch"
DEFAULT_SRC="${KISSAT_SRC:-$ROOT/scratch/kissat}"
DEFAULT_OUT="${KISSAT_TRACED_BIN:-${TMPDIR:-/tmp}/kissat-traced}"

SRC_DIR="${1:-$DEFAULT_SRC}"
OUT_BIN="${2:-$DEFAULT_OUT}"
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
