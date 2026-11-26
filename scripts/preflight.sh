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
timeout 30 python3 -B - "$BASE" "$ROOT" <<'PY'
import pathlib
import subprocess
import sys

base = sys.argv[1]
root = pathlib.Path(sys.argv[2])
sys.path.insert(0, str(root / "scripts"))
from lean_imports import (
    DEFAULT_MAX_COL,
    DEFAULT_MAX_LOC,
    DEFAULT_MAX_PROOF_THM_LOC,
    audit_lean_source,
)

changed: set[str] = set()
cmds = [
    ["git", "diff", "--name-only", "HEAD"],
    ["git", "ls-files", "--others", "--exclude-standard"],
]
has_base = (
    subprocess.run(
        ["git", "rev-parse", "--verify", f"{base}^{{commit}}"],
        capture_output=True,
        check=False,
    ).returncode
    == 0
)
base_tree_ref: str | None = None
if has_base:
    cmds.insert(0, ["git", "diff", "--name-only", f"{base}...HEAD"])
    mb = subprocess.run(
        ["git", "merge-base", base, "HEAD"],
        capture_output=True,
        text=True,
        check=False,
    )
    base_tree_ref = mb.stdout.strip() if mb.returncode == 0 else base
elif (
    subprocess.run(
        ["git", "rev-parse", "--verify", "HEAD^{commit}"],
        capture_output=True,
        check=False,
    ).returncode
    == 0
):
    base_tree_ref = "HEAD"

for cmd in cmds:
    r = subprocess.run(cmd, capture_output=True, text=True, check=False)
    if r.returncode == 0:
        changed.update(
            ln.strip()
            for ln in r.stdout.splitlines()
            if ln.strip().endswith(".lean")
            and not ln.strip().startswith("bv_decide_qbe/")
        )


def read_base_loc(rel_path: str) -> int | None:
    if base_tree_ref is None:
        return None
    res = subprocess.run(
        ["git", "-C", str(root), "show", f"{base_tree_ref}:{rel_path}"],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0:
        return None
    return len(res.stdout.splitlines())


errs: list[str] = []
for f in sorted(changed):
    p = root / f
    if not p.is_file():
        continue
    text = p.read_text(encoding="utf-8")
    rep = audit_lean_source(
        f,
        text,
        max_loc=DEFAULT_MAX_LOC,
        max_col=DEFAULT_MAX_COL,
        max_proof_thm_loc=DEFAULT_MAX_PROOF_THM_LOC,
    )
    loc = int(rep["loc"])  # type: ignore[arg-type]
    if rep["over_loc"]:
        base_loc = read_base_loc(f)
        if base_loc is not None and base_loc >= DEFAULT_MAX_LOC:
            if loc > base_loc:
                errs.append(
                    f"{f}: grandfathered file grew {base_loc} -> {loc} LOC "
                    f"(>= {DEFAULT_MAX_LOC})"
                )
        else:
            errs.append(f"{f}: {loc} LOC >= {DEFAULT_MAX_LOC}")
    for ln in rep["conflicts"]:  # type: ignore[attr-defined]
        errs.append(f"{f}:{ln}: merge conflict marker")
    for ln in rep["bad_import_all"]:  # type: ignore[attr-defined]
        errs.append(f"{f}:{ln}: forbidden `import all`")
    for ln in rep["proof_import_all"]:  # type: ignore[attr-defined]
        if ln not in rep["bad_import_all"]:  # type: ignore[operator]
            errs.append(f"{f}:{ln}: forbidden `import all` in Proof/ shard")
    for hit in rep["banned_hits"]:  # type: ignore[attr-defined]
        errs.append(f"{f}:{hit['line']}: forbidden token in `{hit['text']}`")
    for ln in rep["expose_on_thm"]:  # type: ignore[attr-defined]
        errs.append(f"{f}:{ln}: @[expose] on theorem/lemma")
    for sec in rep["proof_expose_section"]:  # type: ignore[attr-defined]
        errs.append(
            f"{f}:{sec['theorem_line']}: theorem/lemma inside file-level "
            f"`@[expose] public section` (line {sec['section_line']})"
        )
    for thm in rep["proof_long_theorems"]:  # type: ignore[attr-defined]
        errs.append(
            f"{f}:{thm['start_line']}: theorem `{thm['name']}` is "
            f"{thm['lines']} lines > {DEFAULT_MAX_PROOF_THM_LOC} "
            f"(L{thm['start_line']}-L{thm['end_line']})"
        )
    for ln_info in rep["long_lines"]:  # type: ignore[attr-defined]
        errs.append(f"{f}:{ln_info['line']}: line width {ln_info['cols']} > {DEFAULT_MAX_COL}")

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
