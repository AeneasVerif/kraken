#!/usr/bin/env bash
# Native x64 + AArch64 differential test suite for LeanQbe.T.{Amd64,Arm64}.Bignum
# (`mul4x4`, `addMod25519`, `subMod25519`).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-tbignum.XXXXXX")}"
cleanup() { if [ -z "$OUT_USER" ]; then rm -rf "$OUT"; fi; }
trap cleanup EXIT
echo "outputs in $OUT"

echo "== 1. build Bignum modules =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 900 lake build --wfail LeanQbe.T.Amd64.Bignum LeanQbe.T.Amd64.PrintATTAlign \
    LeanQbe.T.Arm64.Bignum
else
  echo "SKIP_BUILD=1: skipping lake build LeanQbe.T.Amd64.Bignum LeanQbe.T.Arm64.Bignum"
fi

echo "== 2. emit native assembly =="
timeout 120 lake env lean --run test/t_bignum/emit_x64.lean "$OUT"
timeout 120 lake env lean --run test/t_bignum/emit_arm64.lean "$OUT"

echo "== 3. assemble, link, and run native x64 =="
CC_X64="${CC:-cc}"
timeout 60 "$CC_X64" -O2 -Wall -Wextra -Werror -Wl,-z,noexecstack \
  -o "$OUT/bignum_x64" test/t_bignum/bignum_main.c \
  "$OUT/mul4x4_x64.s" "$OUT/addMod25519_x64.s" "$OUT/subMod25519_x64.s"
timeout 60 "$OUT/bignum_x64"

echo "== 4. assemble, link, and run AArch64 under qemu-aarch64 =="
CC_ARM64="${CC_AARCH64:-aarch64-linux-gnu-gcc}"
QEMU_ARM64="${QEMU_ARM64:-qemu-aarch64 -L /usr/aarch64-linux-gnu}"
rm -f "$OUT/bignum_arm64"
timeout 120 "$CC_ARM64" -O2 -Wall -Wextra -Werror -Wl,-z,noexecstack \
  -o "$OUT/bignum_arm64" test/t_bignum/bignum_main.c \
  "$OUT/mul4x4_arm64.s" "$OUT/addMod25519_arm64.s" "$OUT/subMod25519_arm64.s" \
  2>"$OUT/arm64_cc.log" || { cat "$OUT/arm64_cc.log" >&2; exit 1; }
grep -v -e 'SFrame' "$OUT/arm64_cc.log" >&2 || true
timeout 60 $QEMU_ARM64 "$OUT/bignum_arm64"

echo "== test/t_bignum/run.sh: ALL PASSED =="
