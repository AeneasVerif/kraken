#!/usr/bin/env python3
"""Compute exact non-barrel reverse-import build targets for CHECK_SCOPE=rdeps.

Fails closed (exits 1) so `scripts/check.sh` falls back to `full` (or arch scope)
whenever any deletion/rename, toolchain/gate file, unknown non-Lean file, Kraken
file, empty non-barrel Lean seed set, or `|rdeps| > --max-rdeps` occurs.
"""

from __future__ import annotations

import argparse
import collections
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_imports import LEGACY_CERT_RE, mod_to_rel_path, parse_imports, rel_path_to_mod
from sync_hubs import ALL_HUBS

BARRELS: frozenset[str] = frozenset(ALL_HUBS)

FAIL_CLOSED_FILES: frozenset[str] = frozenset(
    {
        "lakefile.toml",
        "lean-toolchain",
        "lake-manifest.json",
        "scripts/check.sh",
        "scripts/AuditAxioms.lean",
        "scripts/rdeps_scope.py",
        "scripts/lean_imports.py",
        "scripts/sync_hubs.py",
        "scripts/check_firewall.py",
        "scripts/headline.txt",
    }
)

KRAKEN_ROOT_FILES: frozenset[str] = frozenset(
    {
        "Kraken.lean",
        "KrakenAArch64.lean",
        "KrakenBedrock2.lean",
        "KrakenRunnerX64.lean",
        "KrakenRunnerAArch64.lean",
        "Att2Intel.lean",
        "Bedrock2C.lean",
    }
)

SAFE_NONLEAN_RE = re.compile(
    r"^(?:(?:LeanQbe-)?README\.md|NOTES\.md|DEVELOPER\.md|CONTRIBUTING\.md"
    r"|docs/.*|bench/.*"
    r"|test/.*\.(?:c|h|py|sh|cnf|lrat|qbe|txt)"
    r"|scripts/(?:fast_land|tier3_check|all|preflight)\.sh"
    r"|scripts/(?:gen_cert_slices|test_gen_cert_slices|test_infra_speedup"
    r"|merge_lean_imports|select_tests)\.py)$"
)

HEADLINES_D_RE = re.compile(r"^scripts/headlines\.d/[^/]+\.txt$")

EXE_ROOT_TO_TARGET: dict[str, str] = {
    "Main": "leanqbe",
    "MainArm64": "leanqbe-arm64",
}

MAX_SMALL_HEADLINE_MODS = 30


def _read_headline_modules(lines: list[str]) -> set[str]:
    mods: set[str] = set()
    for raw in lines:
        s = raw.strip()
        if not s or s.startswith("#"):
            continue
        parts = s.split()
        if len(parts) >= 2:
            mods.add(parts[0])
    return mods


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
    include_legacy: bool,
) -> set[str] | None:
    """Return module seeds for a modified `scripts/headlines.d/*.txt`, or None to fail closed."""
    path = root / rel_str
    if not path.is_file():
        return None
    if ("legacy" in path.name) and not include_legacy:
        return set()
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


def _is_kraken_path(rel: Path) -> bool:
    return (bool(rel.parts) and rel.parts[0] == "Kraken") or (rel.name in KRAKEN_ROOT_FILES)


def compute_rdeps(
    root: Path,
    changed: list[str],
    *,
    max_rdeps: int = 250,
    base: str | None = None,
    include_legacy: bool = False,
) -> list[str] | None:
    """Return sorted affected module names, or `None` when failing closed to `full`."""
    if not changed:
        return None

    lean_changed: set[str] = set()
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
                lean_changed.add(mod)
        elif HEADLINES_D_RE.fullmatch(f):
            hseeds = _collect_headline_seeds(root, f, base, include_legacy)
            if hseeds is None:
                return None
            headline_seeds.update(hseeds)
        elif SAFE_NONLEAN_RE.fullmatch(f):
            continue
        else:
            return None  # unknown build/script/config file -> fail closed

    seeds = sorted(lean_changed | headline_seeds)
    if not seeds or len(seeds) > max_rdeps:
        return None

    # Build reverse import graph over all tracked/untracked non-barrel Lean modules.
    raw_ls = subprocess.check_output(
        [
            "git",
            "-C",
            str(root),
            "ls-files",
            "-z",
            "--cached",
            "--others",
            "--exclude-standard",
            "*.lean",
        ]
    )
    seed_set = set(seeds)
    rgraph: dict[str, list[str]] = collections.defaultdict(list)
    for blob in raw_ls.split(b"\0"):
        if not blob:
            continue
        rel = Path(blob.decode("utf-8"))
        if _is_kraken_path(rel):
            continue
        mod = rel_path_to_mod(rel)
        if mod in BARRELS:
            continue
        if not include_legacy and mod not in seed_set:
            if rel.parts and rel.parts[0] == "LeanQbeLegacyTest":
                continue
            if LEGACY_CERT_RE.match(mod):
                continue
        full = root / rel
        if not full.is_file():
            continue
        _, imps = parse_imports(full)
        for imp in imps:
            if imp.module not in BARRELS:
                rgraph[imp.module].append(mod)

    seen = set(seeds)
    q: collections.deque[str] = collections.deque(seeds)
    while q:
        cur = q.popleft()
        for nxt in rgraph.get(cur, ()):
            if nxt not in seen:
                seen.add(nxt)
                if len(seen) > max_rdeps:
                    return None
                q.append(nxt)

    return sorted(seen)


def modules_to_lake_targets(mods: list[str]) -> list[str]:
    """Map executable root modules (`Main`, `MainArm64`) to Lake exe targets."""
    targets = [EXE_ROOT_TO_TARGET.get(m, m) for m in mods]
    return sorted(set(targets))


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
        help="Optional git base ref for scoping modified scripts/headlines.d/*.txt.",
    )
    ap.add_argument(
        "--max-rdeps",
        type=int,
        default=250,
        help="Fail closed to full if |rdeps| exceeds this cap (default: 250).",
    )
    ap.add_argument(
        "--include-legacy",
        action="store_true",
        help="Include LeanQbeLegacy* modules in reverse-dependency traversal.",
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
        include_legacy=args.include_legacy,
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
