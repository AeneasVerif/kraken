#!/usr/bin/env bash
# <2s local pre-flight gate before launching any `lake build` or posting `[done]`.
# Usage: scripts/preflight.sh [BASE_REF]
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BASE="${1:-HEAD~1}"

echo "== preflight: 1. whitespace & conflict markers =="
if git rev-parse --verify "${BASE}^{commit}" >/dev/null 2>&1; then
  git diff --check "$BASE"
else
  git diff --check
fi

echo "== preflight: 2. firewall & strict hub sync (<1s) =="
timeout 30 python3 -B scripts/check_firewall.py --root "$ROOT" --require-isa
timeout 30 python3 -B scripts/sync_hubs.py --root "$ROOT" --check --strict

echo "== preflight: 3. changed .lean hygiene (tokens, <2500 LOC, <=100c, @[expose], P0-5) =="
timeout 30 python3 -B scripts/lean_imports.py preflight-hygiene "$BASE" "$ROOT"

# 4. If any Kissat C0 source changed, run <1s C99 extract + clang syntax/warning check!
kissat_c0_changed="$({
  if git rev-parse --verify "${BASE}^{commit}" >/dev/null 2>&1; then
    git diff --name-only "$BASE" 2>/dev/null || true
  else
    git diff --name-only HEAD 2>/dev/null || true
  fi
  git ls-files --others --exclude-standard LeanQbe/T/Examples/Kissat 2>/dev/null || true
} | sort -u \
  | grep -E '^LeanQbe/T/Examples/Kissat/[^/]*\.lean$' \
  | grep -vE '(Proof|Lemmas|Spec|Arena|Inl|Hub|Bridge|Nv|SatSound)[0-9]*\.lean$' || true)"

if [ -n "$kissat_c0_changed" ]; then
  echo "== preflight: 4. Kissat C0-direct C99 syntax & warning fail-fast (<1s) =="
  TMP_C="$(mktemp "${TMPDIR:-/tmp}/preflight-c0.XXXXXX.c")"
  trap 'rm -f "$TMP_C"' EXIT
  TGT="m7fidelity"
  [ -f LeanQbe/T/Examples/Kissat/FullFidelityAssembly.lean ] && TGT="fidelity"
  timeout 30 python3 -B bench/kissat/extract_c0_direct.py --target "$TGT" --out "$TMP_C"
  timeout 30 clang -std=c99 -O2 -fwrapv -fno-strict-aliasing -Wall -Wextra -Werror \
    -ILeanQbe/T/Frontend/C0 -fsyntax-only "$TMP_C"
  echo "preflight C0-direct ($TGT): OK (c0_sha256=$(sha256sum "$TMP_C" | awk '{print $1}'))"
fi

echo "== preflight: ALL PASSED =="
