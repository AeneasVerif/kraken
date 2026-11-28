#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

RUN_SCOPE=(
  systemd-run --user --scope --quiet
  --slice=leanqbe-builds.slice
  -p MemoryMax=18G -p MemorySwapMax=0 -p OOMPolicy=kill
  env LAKE_ARTIFACT_CACHE=true LAKE_RESTORE_ARTIFACTS=true LEAN_NUM_THREADS=1
)

echo "== [1/8] scan bv_decide_qbe/*.lean for forbidden tokens (0 axiom/sorry/native_decide) =="
timeout 60 python3 -B - <<'PY'
import pathlib, re, sys

files = sorted(pathlib.Path(".").rglob("*.lean"))
files = [f for f in files if ".lake" not in f.parts]

def strip_lean(src: str) -> str:
    out = []
    i = 0
    n = len(src)
    depth = 0
    in_str = False
    while i < n:
        ch = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if depth > 0:
            if ch == "/" and nxt == "-":
                depth += 1; i += 2; continue
            if ch == "-" and nxt == "/":
                depth -= 1; i += 2; continue
            if ch == "\n":
                out.append("\n")
            i += 1; continue
        if in_str:
            if ch == "\\" and i + 1 < n:
                if src[i + 1] == "\n": out.append("\n")
                i += 2; continue
            if ch == '"':
                in_str = False; i += 1; continue
            if ch == "\n": out.append("\n")
            i += 1; continue
        if ch == "-" and nxt == "-":
            while i < n and src[i] != "\n":
                i += 1
            continue
        if ch == "/" and nxt == "-":
            depth = 1; i += 2; continue
        if ch == '"':
            in_str = True; out.append('""'); i += 1; continue
        out.append(ch)
        i += 1
    return "".join(out)

tok_re = re.compile(
    r"\b(?:sorry|admit|bv_decide|native_decide|ofReduceBool|ofReduceNat|trustCompiler)\b"
    r"|decide\s+\+native"
)
axiom_re = re.compile(
    r"(?:^|;)\s*(?:(?:public|private|protected|unsafe|noncomputable|local|scoped)\s+)*axiom\b"
)
imp_by_re = re.compile(r"@\[[^\]]*\bimplemented_by\b")

hits = []
for f in files:
    cleaned = strip_lean(f.read_text(encoding="utf-8"))
    for lineno, line in enumerate(cleaned.splitlines(), 1):
        if tok_re.search(line) or axiom_re.search(line) or imp_by_re.search(line):
            hits.append(f"{f}:{lineno}: {line.strip()}")

if hits:
    print("\n".join(hits), file=sys.stderr)
    sys.exit(1)
print(f"token scan: OK ({len(files)} .lean files, 0 axiom / 0 sorry / 0 native_decide)")
PY

echo "== [2/8] lake build (Syntax + Native + Plugin + BvDecideQbe + Test + libkissat_qbe) =="
timeout 3600 "${RUN_SCOPE[@]}" lake build BvDecideQbeSyntax BvDecideQbeNative BvDecideQbePlugin BvDecideQbe BvDecideQbeTest

echo "== [3/8] check .globl hygiene in kissat_solver.s =="
ASM_PATH=".lake/build/c/kissat_solver.s"
test -f "$ASM_PATH"
GLOBLS="$(grep -E '^[[:space:]]*\.globl[[:space:]]+' "$ASM_PATH" | awk '{print $2}' | tr '\n' ' ')"
echo "assembly .globl symbols: $GLOBLS"
if [ "$GLOBLS" != "bv_solve_bytes " ]; then
  echo "ERROR: expected ONLY '.globl bv_solve_bytes', got: $GLOBLS" >&2
  exit 1
fi
tail -n 3 "$ASM_PATH" | grep -q '\.note\.GNU-stack'

echo "== [4/8] readelf -d TEXTREL == 0 check =="
SO_FILES=()
while IFS= read -r -d '' so; do
  SO_FILES+=("$so")
done < <(find .lake/build/lib -name '*.so' -print0)
if [ "${#SO_FILES[@]}" -eq 0 ]; then
  echo "ERROR: no built .so files found under .lake/build/lib" >&2
  exit 1
fi
for so in "${SO_FILES[@]}"; do
  if readelf -d "$so" | grep -q TEXTREL; then
    echo "ERROR: TEXTREL found in $so" >&2
    readelf -d "$so" | grep TEXTREL >&2
    exit 1
  fi
  echo "TEXTREL=0: $so"
done

echo "== [5/8] clang -fsanitize=address,undefined c_det_test.c (4-mmap x 2 runs + guarded_buf.h) =="
LEAN_INC="$(lean --print-prefix)/include"
TMP_BIN="$(mktemp "${TMPDIR:-/tmp}/c_det_test.XXXXXX")"
trap 'rm -f "$TMP_BIN"' EXIT
timeout 120 clang -std=c99 -O1 -g -fsanitize=address,undefined \
  -Wall -Wextra -Werror \
  -I"$LEAN_INC" \
  BvDecideQbeTest/c_det_test.c c/kissat_ffi.c "$ASM_PATH" \
  -o "$TMP_BIN"
timeout 120 "$TMP_BIN"

echo "== [6/8] live in-process Lean FfiTest (precompileModules dlopen + differential checks) =="
timeout 600 "${RUN_SCOPE[@]}" lake lean BvDecideQbeTest/FfiTest.lean

echo "== [7/8] live in-process Lean EncodeCexTest (round-trip + sizing + CEX evalEfficient) =="
timeout 600 "${RUN_SCOPE[@]}" lake lean BvDecideQbeTest/EncodeCexTest.lean

echo "== [8/8] live in-process Lean UnitTest + CutTest (bv_decide_qbe + bv_cut_qbe + ring + rules) =="
timeout 600 "${RUN_SCOPE[@]}" lake lean BvDecideQbeTest/UnitTest.lean
timeout 600 "${RUN_SCOPE[@]}" lake lean BvDecideQbeTest/CutTest.lean

echo "== bv_decide_qbe/scripts/check.sh: ALL PASSED =="
