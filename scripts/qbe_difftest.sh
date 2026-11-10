#!/usr/bin/env bash
# Differential test of LeanQbe's operation semantics and printer against stock QBE.
# Usage: scripts/qbe_difftest.sh [workdir]   (default: a fresh temporary directory)
# Builds stock QBE from a copy of $QBE_SRC (default ./qbe, else the original checkout; never inside it)
# unless $QBE points to a qbe binary.
# Runs amd64 natively, and arm64 under qemu-aarch64 if aarch64-linux-gnu-gcc and qemu-aarch64 exist.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
W="${1:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-qbediff.XXXXXX")}"
mkdir -p "$W"
if [ -z "${QBE:-}" ]; then
  QBE_SRC="${QBE_SRC:-$ROOT/qbe}"
  [ -d "$QBE_SRC" ] || QBE_SRC=/usr/local/google/home/andreser/lean-qbe/qbe
  rm -rf "$W/qbe-src" && cp -r "$QBE_SRC" "$W/qbe-src"
  timeout 300 make -C "$W/qbe-src" -j8 >/dev/null 2>&1
  QBE="$W/qbe-src/qbe"
fi
cd "$ROOT"
timeout 300 lake build spike.il.Smoke >/dev/null
timeout 600 lake env lean --run scripts/QbeDiff.lean "$W/out"
cd "$W/out"
timeout 60 "$QBE" -o test.s test.ssa
timeout 300 cc -O0 -o t harness.c test.s
timeout 120 ./t > got.txt
timeout 60 ./t exit > got_exit.txt || true
diff expected.txt got.txt > diff.txt && diff expected_exit.txt got_exit.txt >> diff.txt \
  && echo "amd64: $(cat got.txt got_exit.txt | wc -l) results match" || { echo "amd64: MISMATCH"; head -20 diff.txt; exit 1; }
if command -v aarch64-linux-gnu-gcc >/dev/null && command -v qemu-aarch64 >/dev/null; then
  timeout 60 "$QBE" -t arm64 -o test_a64.s test.ssa
  timeout 300 aarch64-linux-gnu-gcc -O0 -o ta harness.c test_a64.s 2>&1 | grep -v SFrame || true
  timeout 300 qemu-aarch64 -L /usr/aarch64-linux-gnu ./ta > got_a64.txt
  timeout 60 qemu-aarch64 -L /usr/aarch64-linux-gnu ./ta exit > got_exit_a64.txt || true
  diff expected.txt got_a64.txt > diff_a64.txt && diff expected_exit.txt got_exit_a64.txt >> diff_a64.txt \
    && echo "arm64: $(cat got_a64.txt got_exit_a64.txt | wc -l) results match" || { echo "arm64: MISMATCH"; head -20 diff_a64.txt; exit 1; }
fi
