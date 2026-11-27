#!/usr/bin/env python3
"""Path-gated runtime test suite dispatcher for `scripts/fast_land.sh`.

Maps changed paths in `BASE..HEAD` (or an explicit `--files` list) to the
minimal set of runtime test suites needed, returning 0 suites on proof-only,
doc-only, or pure-gate/script diffs while failing closed on core compiler/ISA
or ambiguous executable changes.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_imports import BARREL_PATHS

# Canonical execution order for deterministic output.
SUITE_ORDER: tuple[str, ...] = (
    "./test/run.sh",
    "./test/arm64/run.sh",
    "./test/c0/run.sh",
    "./test/lcnf/run.sh",
    "./test/lrc/run.sh",
    "./test/bootstrap0/run_stage_c_native.sh",
    "./test/cpp/run.sh",
    "./test/t_qbe/run.sh",
    "./test/t_lrat/run.sh",
    "./tool/test_lrat_check.sh",
    "./test/t_bignum/run.sh",
    "./test/t_chacha/run.sh",
    "bash ./bench/kissat/build_c0_direct.sh --asan",
    "./test/kissat/run.sh",
)

DOC_ONLY_RE = re.compile(
    r"^(?:.*\.md|docs/.*|img/.*|scripts/headlines\.d/.*|scripts/headline\.txt|\.gitignore)$"
)

SCRIPT_ONLY_RE = re.compile(r"^scripts/.*\.(?:sh|py|lean)$")

PROOF_LEAN_RE = re.compile(
    r"(?:Proof|Lemmas|Audit|Spec|Bridge|Nv|SatSound)[0-9]*\.lean$"
)

CERT_LEAN_RE = re.compile(
    r"^LeanQbe/T/(?:Amd64|Arm64)/Kissat.*(?:Cert|Bounds|Sound)?[0-9a-z]*\.lean$"
)

TEST_TREE_RE = re.compile(
    r"^(?:LeanQbeTest|LeanQbeBootstrap0Test)/.*\.lean$"
)

EXEC_DECL_RE = re.compile(
    r"\b(?:def|abbrev|structure|inductive|class|instance|macro|syntax|elab"
    r"|opaque|partial|unsafe)\b|kissat_c0!|c0_file!|def_c0!|compile_linked_chunks!"
)

PROOF_LINE_RE = re.compile(
    r"^(?:--.*|/-.*|.*-/|\*.*|import\b|public\s+import\b|meta\s+import\b"
    r"|private\s+import\b|open\b|namespace\b|end\b|section\b|public\s+section\b"
    r"|set_option\b|attribute\b|theorem\b|lemma\b|private\s+theorem\b"
    r"|private\s+lemma\b|example\b|#print\b|#check\b|#guard\b|by\b|have\b"
    r"|show\b|exact\b|apply\b|refine\b|rw\b|simp\b|simpa\b|intro\b|intros\b"
    r"|cases\b|rcases\b|obtain\b|constructor\b|omega\b|decide\b|rfl\b"
    r"|funext\b|ext\b|calc\b|unfold\b|dsimp\b|change\b|subst\b|clear\b"
    r"|rename_i\b|t_kernel_rfl\b|\|.*)$"
)

KISSAT_SUITE_FILES_RE = re.compile(
    r"^LeanQbe/T/Examples/Kissat/(?:Solver|Plain|FullM3|FullM4|Core|Dimacs)[^/]*\.lean$"
)


def _is_proof_only_diff(root: Path, base: str, head: str, rel: str) -> bool:
    """Conservatively check if a `.lean` diff hunk only touches proofs/comments."""
    res = subprocess.run(
        ["git", "-C", str(root), "diff", "--unified=0", f"{base}..{head}", "--", rel],
        capture_output=True,
        text=True,
        check=False,
    )
    if res.returncode != 0 or not res.stdout.strip():
        return False
    changed_lines: list[str] = []
    for ln in res.stdout.splitlines():
        if ln.startswith(("+++", "---", "@@")):
            continue
        if ln.startswith(("+", "-")):
            s = ln[1:].strip()
            if s:
                changed_lines.append(s)
    if not changed_lines:
        return True
    for s in changed_lines:
        if EXEC_DECL_RE.search(s):
            return False
        if not PROOF_LINE_RE.match(s):
            return False
    return True


def select_suites(
    changed: list[str],
    *,
    root: Path | None = None,
    base: str | None = None,
    head: str | None = None,
) -> list[str]:
    """Return ordered runtime test commands required for `changed` files."""
    selected: set[str] = set()

    for raw in changed:
        f = raw.strip()
        if not f:
            continue
        if DOC_ONLY_RE.fullmatch(f) or SCRIPT_ONLY_RE.fullmatch(f):
            continue
        if f in BARREL_PATHS or TEST_TREE_RE.fullmatch(f):
            continue
        if f.endswith(".lean"):
            if CERT_LEAN_RE.fullmatch(f) or PROOF_LEAN_RE.search(f):
                continue
            if root and base and head and _is_proof_only_diff(root, base, head, f):
                continue

        # Subsystem routing
        if f.startswith(("LeanQbe/T/Frontend/C0/", "LeanQbe/T/Frontend/C0.lean", "test/c0/")):
            selected.add("./test/c0/run.sh")
        elif f.startswith(("LeanQbe/T/LeanLCNF/", "test/lcnf/")):
            selected.add("./test/lcnf/run.sh")
        elif f.startswith(("LeanQbe/T/LeanLRC/", "test/lrc/")):
            selected.add("./test/lrc/run.sh")
        elif f.startswith(("LeanQbe/T/Bootstrap0/", "test/bootstrap0/")):
            selected.add("./test/bootstrap0/run_stage_c_native.sh")
        elif f.startswith(("LeanQbe/T/Examples/Kissat/", "bench/kissat/", "test/kissat/")):
            if f.startswith("test/kissat/") or KISSAT_SUITE_FILES_RE.fullmatch(f):
                selected.add("./test/kissat/run.sh")
            else:
                selected.add("bash ./bench/kissat/build_c0_direct.sh --asan")
        elif f in ("LeanQbe/T/PrintCpp.lean",) or f.startswith(("LeanQbe/T/Runtime/", "test/cpp/")):
            selected.update({"./test/cpp/run.sh", "./test/t_lrat/run.sh"})
        elif f == "LeanQbe/T/PrintQbe.lean" or f.startswith("test/t_qbe/"):
            selected.add("./test/t_qbe/run.sh")
        elif (
            f.startswith("LeanQbe/T/Examples/LratBytes")
            or f.startswith("tool/")
            or f.startswith("test/t_lrat/")
        ):
            selected.update({"./test/t_lrat/run.sh", "./tool/test_lrat_check.sh"})
        elif (
            re.match(r"^LeanQbe/T/(?:Amd64|Arm64|Examples)/Bignum", f)
            or f.startswith("test/t_bignum/")
        ):
            selected.add("./test/t_bignum/run.sh")
        elif (
            re.match(r"^LeanQbe/T/(?:Amd64|Arm64|Examples)/ChaCha", f)
            or f.startswith("test/t_chacha/")
        ):
            selected.add("./test/t_chacha/run.sh")
        elif f.startswith("test/arm64/"):
            selected.add("./test/arm64/run.sh")
        elif f.startswith("test/common/"):
            selected.update({"./test/run.sh", "./test/arm64/run.sh"})
        elif f.startswith("test/"):
            selected.add("./test/run.sh")
        elif f.startswith("LeanQbe/T/Amd64/") or f == "Main.lean":
            selected.update({"./test/run.sh", "./test/kissat/run.sh"})
        elif f.startswith("LeanQbe/T/Arm64/") or f == "MainArm64.lean":
            selected.update({"./test/arm64/run.sh", "./test/kissat/run.sh"})
        else:
            # Core compiler / IR / Kraken / toolchain / unknown file -> fail closed.
            selected.update({"./test/run.sh", "./test/arm64/run.sh", "./test/kissat/run.sh"})

    return [s for s in SUITE_ORDER if s in selected]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Select runtime test suites affected by a git diff or path list."
    )
    ap.add_argument("--root", default=".", help="Repository root (default: .)")
    ap.add_argument(
        "--files",
        default=None,
        help="Read changed repo-relative paths from file (or '-' for stdin) instead of git diff.",
    )
    ap.add_argument("base", nargs="?", default=None, help="Git base commit/ref.")
    ap.add_argument(
        "head",
        nargs="?",
        default="HEAD",
        help="Git target commit/ref (default: HEAD).",
    )
    args = ap.parse_args(argv)

    root = Path(args.root).resolve()
    if args.files is not None:
        raw = (
            sys.stdin.read()
            if args.files == "-"
            else Path(args.files).read_text(encoding="utf-8")
        )
        changed = [ln.strip() for ln in raw.splitlines() if ln.strip()]
        suites = select_suites(changed)
    else:
        if not args.base:
            ap.error("provide either --files or BASE [HEAD]")
        res = subprocess.run(
            ["git", "-C", str(root), "diff", "--name-only", f"{args.base}..{args.head}"],
            capture_output=True,
            text=True,
            check=True,
        )
        changed = [ln.strip() for ln in res.stdout.splitlines() if ln.strip()]
        suites = select_suites(changed, root=root, base=args.base, head=args.head)

    for s in suites:
        print(s)
    return 0


if __name__ == "__main__":
    sys.exit(main())
