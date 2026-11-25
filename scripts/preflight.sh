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

echo "== preflight: 3. changed .lean hygiene (tokens, <=3000 LOC, <=100c, 0 LeanQbe import all) =="
timeout 30 python3 -B - "$BASE" "$ROOT" <<'PY'
import pathlib
import re
import subprocess
import sys

base = sys.argv[1]
root = pathlib.Path(sys.argv[2])
sys.path.insert(0, str(root / "scripts"))
from lean_imports import strip_comments_line

changed: set[str] = set()
cmds = [
    ["git", "diff", "--name-only", "HEAD"],
    ["git", "ls-files", "--others", "--exclude-standard"],
]
if subprocess.run(
    ["git", "rev-parse", "--verify", f"{base}^{{commit}}"],
    capture_output=True,
    check=False,
).returncode == 0:
    cmds.insert(0, ["git", "diff", "--name-only", f"{base}...HEAD"])

for cmd in cmds:
    r = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if r.returncode == 0:
        changed.update(
            ln.strip() for ln in r.stdout.splitlines() if ln.strip().endswith(".lean")
        )

tok_re = re.compile(
    r"\b(?:sorry|admit|bv_decide|native_decide|ofReduceBool|ofReduceNat|trustCompiler)\b"
    r"|decide\s+\+native"
    r"|@\[[^\]]*\b(?:implemented_by|extern)\b"
)
imp_all_bad_re = re.compile(
    r"^\s*(?:public\s+(?:meta\s+)?import\s+all\b|(?:meta\s+)?import\s+all\s+LeanQbe\b)"
)
conflict_re = re.compile(r"^(?:<{7}|={7}|>{7})(?: |$)")
str_re = re.compile(r'"(?:\\.|[^"\\])*"')

errs: list[str] = []
for f in sorted(changed):
    p = root / f
    if not p.is_file():
        continue
    lines = p.read_text(encoding="utf-8").splitlines()
    if len(lines) > 3000:
        errs.append(f"{f}: {len(lines)} LOC > 3000")
    depth = 0
    for idx, ln in enumerate(lines, 1):
        if conflict_re.match(ln):
            errs.append(f"{f}:{idx}: merge conflict marker")
        code, depth, _ = strip_comments_line(ln, depth)
        if code:
            if imp_all_bad_re.match(code):
                errs.append(f"{f}:{idx}: forbidden `{code.strip()}`")
            code_nostr = str_re.sub('""', code)
            if tok_re.search(code_nostr):
                errs.append(f"{f}:{idx}: forbidden token in `{code.strip()[:80]}`")
        if len(ln) > 100 and not ln.strip().startswith(("--", "/-", '"')):
            errs.append(f"{f}:{idx}: line width {len(ln)} > 100")

if errs:
    print("\n".join(f"FAIL: {e}" for e in errs[:40]), file=sys.stderr)
    sys.exit(1)
print(f"preflight .lean hygiene: OK ({len(changed)} changed file(s))")
PY

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
