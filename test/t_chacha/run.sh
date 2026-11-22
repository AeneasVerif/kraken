#!/usr/bin/env bash
# Native x64 + AArch64 RFC 8439 §2.3.2 and differential test suite for
# LeanQbe.T.{Amd64,Arm64}.ChaCha (`chacha20Block`).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT"

OUT_USER="${OUT+set}"
OUT="${OUT:-$(mktemp -d "${TMPDIR:-/tmp}/leanqbe-tchacha.XXXXXX")}"
cleanup() { if [ -z "$OUT_USER" ]; then rm -rf "$OUT"; fi; }
trap cleanup EXIT
echo "outputs in $OUT"

echo "== 1. build ChaCha modules =="
if [ "${SKIP_BUILD:-0}" != "1" ]; then
  timeout 900 lake build --wfail LeanQbe.T.Amd64.ChaCha LeanQbe.T.Arm64.ChaCha
else
  echo "SKIP_BUILD=1: skipping lake build LeanQbe.T.Amd64.ChaCha LeanQbe.T.Arm64.ChaCha"
fi

echo "== 2. emit native assembly =="
timeout 120 lake env lean --run test/t_chacha/emit_x64.lean "$OUT"
timeout 120 lake env lean --run test/t_chacha/emit_arm64.lean "$OUT"

echo "== 3. assemble, link, and run native x64 =="
CC_X64="${CC:-cc}"
timeout 60 "$CC_X64" -O2 -Wall -Wextra -Werror -Wl,-z,noexecstack \
  -o "$OUT/chacha_x64" test/t_chacha/chacha_main.c "$OUT/chacha_x64.s"
timeout 60 "$OUT/chacha_x64"

echo "== 4. assemble, link, and run AArch64 under qemu-aarch64 =="
CC_ARM64="${CC_AARCH64:-aarch64-linux-gnu-gcc}"
QEMU_ARM64="${QEMU_ARM64:-qemu-aarch64 -L /usr/aarch64-linux-gnu}"
rm -f "$OUT/chacha_arm64"
timeout 120 "$CC_ARM64" -O2 -Wall -Wextra -Werror -Wl,-z,noexecstack \
  -o "$OUT/chacha_arm64" test/t_chacha/chacha_main.c "$OUT/chacha_arm64.s" \
  2>"$OUT/arm64_cc.log" || { cat "$OUT/arm64_cc.log" >&2; exit 1; }
grep -v -e 'SFrame' "$OUT/arm64_cc.log" >&2 || true
timeout 60 $QEMU_ARM64 "$OUT/chacha_arm64"

echo "== test/t_chacha/run.sh: ALL PASSED =="
