#!/usr/bin/env python3
"""Compute exact non-barrel reverse-import build targets for CHECK_SCOPE=rdeps.

Fails closed (exits 1) so `scripts/check.sh` falls back to `full` (or arch scope)
whenever any deletion/rename, toolchain/gate file, unknown non-Lean file, Kraken
file, empty non-barrel Lean seed set, or `|rdeps| > --max-rdeps` occurs.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_imports import (
    BARRELS,
    classify_git_edit_kind,
    collect_lean_rdeps,
    is_kraken_path,
    mod_to_rel_path,
    modules_to_lake_targets,
    read_headline_entries,
    rel_path_to_mod,
)

_is_kraken_path = is_kraken_path

FAIL_CLOSED_FILES: frozenset[str] = frozenset(
    {
        "lakefile.toml",
        "lean-toolchain",
        "lake-manifest.json",
        "scripts/check.sh",
        "scripts/common.sh",
        "scripts/_common.py",
        "scripts/AuditAxioms.lean",
        "scripts/rdeps_scope.py",
        "scripts/lean_imports.py",
        "scripts/sync_hubs.py",
        "scripts/check_firewall.py",
        "scripts/headline.txt",
    }
)

SAFE_NONLEAN_RE = re.compile(
    r"^(?:(?:LeanQbe-)?README\.md|NOTES\.md|DEVELOPER\.md|CONTRIBUTING\.md"
    r"|docs/.*|img/.*|bench/.*"
    r"|test/.*\.(?:c|h|py|sh|cnf|lrat|qbe|txt)"
    r"|scripts/(?:fast_land|all|preflight)\.sh"
    r"|scripts/(?:gen_cert_slices|test_gen_cert_slices|test_infra_speedup"
    r"|merge_lean_imports|select_tests)\.py)$"
)

HEADLINES_D_RE = re.compile(r"^scripts/headlines\.d/[^/]+\.txt$")
MAX_SMALL_HEADLINE_MODS = 30


def _read_headline_modules(lines: list[str]) -> set[str]:
    return {mod for mod, _ in read_headline_entries(lines)}


def _is_tracked(root: Path, rel_str: str) -> bool:
    res = subprocess.run(
        ["git", "-C", str(root), "ls-files", "--error-unmatch", "--", rel_str],
        capture_output=True,
        check=False,
    )
    return res.returncode == 0


def _added_headline_lines(root: Path, rel_str: str, base: str | None) -> list[str] | None:
    """Return added/changed lines from `rel_str` against `base` (or None if unavailable)."""
    if not base:
        return None
    added: list[str] = []
    for cmd in (
        ["git", "-C", str(root), "diff", "--unified=0", f"{base}...HEAD", "--", rel_str],
        ["git", "-C", str(root), "diff", "--unified=0", "HEAD", "--", rel_str],
    ):
        res = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if res.returncode != 0:
            return None
        for ln in res.stdout.splitlines():
            if ln.startswith("+") and not ln.startswith("+++"):
                added.append(ln[1:])
    return added


def _collect_headline_seeds(
    root: Path,
    rel_str: str,
    base: str | None,
) -> set[str] | None:
    """Return module seeds for a modified `scripts/headlines.d/*.txt`, or None to fail closed."""
    path = root / rel_str
    if not path.is_file():
        return None
    all_mods = _read_headline_modules(path.read_text(encoding="utf-8").splitlines())
    if (not _is_tracked(root, rel_str)) or len(all_mods) <= MAX_SMALL_HEADLINE_MODS:
        seeds = all_mods
    else:
        added = _added_headline_lines(root, rel_str, base)
        if added is None:
            return None
        seeds = _read_headline_modules(added)
    for mod in seeds:
        if not (root / mod_to_rel_path(mod)).is_file():
            return None
    return seeds


def compute_rdeps(
    root: Path,
    changed: list[str],
    *,
    max_rdeps: int = 250,
    base: str | None = None,
    trace_mode: str = "lake",
    edit_kind: str = "olean",
) -> list[str] | None:
    """Return sorted affected module names, or `None` when failing closed to `full`.

    `trace_mode`:
      - `'lake'` (default): exact Lean 4.37 / Lake 5.0 trace propagation
        (`transTrace`, `metaTransTrace`, `allTransTrace`, `legacyTransTrace`).
      - `'graph'`: legacy edge-uniform reverse-import BFS.
    `edit_kind`:
      - `'olean'` (default): conservative public-interface change.
      - `'ir'`: private / unexposed `def` body change (`.ir` only).
      - `'proof'`: theorem proof-body / comment-only change (`.olean.private` only).
      - `'auto'`: classify each changed `.lean` file against `base` (falls back
        conservatively to `'olean'` when `base` is absent or diff touches any
        header/signature/non-theorem line).
    """
    if not changed:
        return None
    if trace_mode not in ("lake", "graph"):
        raise ValueError(f"invalid trace_mode: {trace_mode!r}")
    if edit_kind not in ("olean", "ir", "proof", "auto"):
        raise ValueError(f"invalid edit_kind: {edit_kind!r}")

    lean_changed: dict[str, str] = {}
    headline_seeds: set[str] = set()
    for raw in changed:
        f = raw.strip()
        if not f:
            continue
        if f in FAIL_CLOSED_FILES:
            return None
        p = root / f
        if not p.is_file():
            return None  # deletion/rename -> fail closed
        if f.endswith(".lean"):
            rel = Path(f)
            if _is_kraken_path(rel):
                return None
            mod = rel_path_to_mod(rel)
            if mod not in BARRELS:
                lean_changed[mod] = f
        elif HEADLINES_D_RE.fullmatch(f):
            hseeds = _collect_headline_seeds(root, f, base)
            if hseeds is None:
                return None
            headline_seeds.update(hseeds)
        elif SAFE_NONLEAN_RE.fullmatch(f):
            continue
        else:
            return None  # unknown build/script/config file -> fail closed

    seeds = sorted(set(lean_changed) | headline_seeds)
    if not seeds or len(seeds) > max_rdeps:
        return None

    seed_edit_kinds: dict[str, str] | None = None
    eff_edit_kind = edit_kind
    if trace_mode == "lake" and edit_kind == "auto":
        eff_edit_kind = "olean"
        seed_edit_kinds = {}
        for mod in seeds:
            if mod in headline_seeds:
                seed_edit_kinds[mod] = "olean"
            else:
                seed_edit_kinds[mod] = classify_git_edit_kind(root, lean_changed[mod], base)

    return collect_lean_rdeps(
        root,
        seeds,
        barrels=BARRELS,
        max_rdeps=max_rdeps,
        trace_mode=trace_mode,
        edit_kind=eff_edit_kind,
        seed_edit_kinds=seed_edit_kinds,
    )


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(
        description="Compute reverse-import Lake build targets for CHECK_SCOPE=rdeps."
    )
    ap.add_argument("--root", default=".", help="Repository root (default: .)")
    ap.add_argument(
        "--changed",
        required=True,
        help="File listing changed repo-relative paths (or '-' for stdin).",
    )
    ap.add_argument(
        "--base",
        default=None,
        help="Optional git base ref for scoping modified scripts/headlines.d/*.txt and --edit-kind auto.",
    )
    ap.add_argument(
        "--max-rdeps",
        type=int,
        default=250,
        help="Fail closed to full if |rdeps| exceeds this cap (default: 250).",
    )
    ap.add_argument(
        "--trace-mode",
        choices=("lake", "graph"),
        default="lake",
        help="Reverse-dependency propagation model: exact Lake 5.0 traces ('lake', default) or uniform graph ('graph').",
    )
    ap.add_argument(
        "--edit-kind",
        choices=("olean", "ir", "proof", "auto"),
        default="olean",
        help="Seed edit kind for --trace-mode lake (default: olean).",
    )
    ap.add_argument(
        "--out-headlines",
        default=None,
        help="Optional output path for affected headline module filter list.",
    )
    ap.add_argument(
        "--check-only",
        action="store_true",
        help="Exit 0 iff rdeps scope is valid; print nothing.",
    )
    args = ap.parse_args(argv)

    root = Path(args.root).resolve()
    if args.changed == "-":
        raw_lines = sys.stdin.read().splitlines()
    else:
        raw_lines = Path(args.changed).read_text(encoding="utf-8").splitlines()
    changed = [ln.strip() for ln in raw_lines if ln.strip()]

    mods = compute_rdeps(
        root,
        changed,
        max_rdeps=args.max_rdeps,
        base=args.base,
        trace_mode=args.trace_mode,
        edit_kind=args.edit_kind,
    )
    if mods is None:
        return 1

    if args.out_headlines:
        Path(args.out_headlines).write_text(
            "\n".join(mods) + ("\n" if mods else ""), encoding="utf-8"
        )
    if not args.check_only:
        for tgt in modules_to_lake_targets(mods):
            print(tgt)
    return 0


if __name__ == "__main__":
    sys.exit(main())
