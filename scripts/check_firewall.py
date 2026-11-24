#!/usr/bin/env python3
"""Static incrementality-firewall linter for LeanQbe module boundaries.

Checks that firewall interface and executable entry modules do not leak proof
lemmas (`*Lemmas*` or `*.Targ`) via `public import`s (Neon Pillar 5 Risk #2):

  - L1 (`MainLemmas`): LeanQbe/T/MainLemmas.lean
  - L2 (`Targ`): LeanQbe/T/{Amd64,Arm64}/Targ.lean
  - L3 (`TargLemmas`): LeanQbe/T/{Amd64,Arm64}/TargLemmas.lean
  - L4 (`Main`/`Isa` boundary): Main.lean, MainArm64.lean,
        LeanQbe/T/{Amd64,Arm64}/Isa.lean

Explicitly allowlisted type-only interfaces (e.g. `LeanQbe.T.MainLemmas` in
`{Amd64,Arm64}/TargLemmas.lean`) are permitted.

Usage:
  python3 scripts/check_firewall.py [--root .] [--report-only] [--json]
"""

from __future__ import annotations

import argparse
import json
import re
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_imports import (
    ImportStmt,
    module_to_path,
    parse_imports,
)

TARG_MOD_RE = re.compile(r"^LeanQbe\.T\.(?:Amd64|Arm64)\.Targ(?:Lemmas)?$")


@dataclass
class Violation:
    """Single firewall leak violation within a leak group."""

    leak_id: str
    file: str
    line: int
    module: str
    kind: str
    detail: str


@dataclass
class LeakGroupReport:
    """Summary of one firewall leak category (L1-L4)."""

    leak_id: str
    label: str
    files: list[str]
    missing_files: list[str] = field(default_factory=list)
    violations: list[Violation] = field(default_factory=list)


def find_transitive_leaks(
    root: Path,
    start_imports: list[ImportStmt],
    cache: dict[Path, list[ImportStmt]],
    skip_prefixes: tuple[str, ...] = (),
) -> list[tuple[str, list[str]]]:
    """Find shortest public-import paths from `start_imports` to `*Lemmas*`."""
    queue: list[tuple[str, list[str]]] = [
        (imp.module, [imp.module])
        for imp in start_imports
        if imp.is_public and not imp.module.startswith(skip_prefixes)
    ]
    visited: set[str] = set()
    hits: list[tuple[str, list[str]]] = []

    while queue:
        mod, chain = queue.pop(0)
        if mod in visited:
            continue
        visited.add(mod)

        if "Lemmas" in mod:
            hits.append((mod, chain))
            continue

        path = module_to_path(root, mod)
        if path is None:
            continue
        if path not in cache:
            _, imps = parse_imports(path)
            cache[path] = imps
        for nxt in cache[path]:
            if nxt.is_public and nxt.module not in visited:
                queue.append((nxt.module, [*chain, nxt.module]))
    return hits


def check_direct_lemmas(
    root: Path,
    leak_id: str,
    rel_files: list[str],
    allowlist: dict[str, set[str]],
    cache: dict[Path, list[ImportStmt]],
) -> list[Violation]:
    """Flag direct `public import`s matching `*Lemmas*` outside `allowlist`."""
    violations: list[Violation] = []
    for rel in rel_files:
        path = root / rel
        if not path.is_file():
            continue
        _, imps = parse_imports(path)
        cache[path] = imps
        allowed = allowlist.get(rel, set())
        for imp in imps:
            if not imp.is_public:
                continue
            if "Lemmas" in imp.module and imp.module not in allowed:
                violations.append(
                    Violation(
                        leak_id=leak_id,
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="direct-lemmas",
                        detail=f"public import of `{imp.module}` matches `*Lemmas*`",
                    )
                )
    return violations


def check_boundary_files(
    root: Path,
    leak_id: str,
    rel_files: list[str],
    cache: dict[Path, list[ImportStmt]],
) -> tuple[list[str], list[Violation]]:
    """Check pure-ISA / executable entry files (`Main`, `MainArm64`, `Isa`)."""
    missing: list[str] = []
    violations: list[Violation] = []

    for rel in rel_files:
        path = root / rel
        if not path.is_file():
            missing.append(rel)
            continue
        _, imps = parse_imports(path)
        cache[path] = imps

        for imp in imps:
            if not imp.is_public:
                continue
            if "Lemmas" in imp.module:
                violations.append(
                    Violation(
                        leak_id=leak_id,
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="direct-lemmas",
                        detail=f"public import of `{imp.module}` matches `*Lemmas*`",
                    )
                )
            elif TARG_MOD_RE.match(imp.module):
                violations.append(
                    Violation(
                        leak_id=leak_id,
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="targ-boundary",
                        detail=(
                            f"public import `{imp.module}` leaks target proof "
                            f"modules (expected `*.Isa`)"
                        ),
                    )
                )

        # Also catch hidden transitive `*Lemmas*` leaks on backend/ISA paths
        # (`Driver` is the shared compiler/example CLI hub outside the target ISA
        # boundary, whereas `Isa.lean` and non-Driver target imports must stay
        # 100% `*Lemmas*`-free).
        already_flagged = {(v.file, v.module) for v in violations}
        skip = ("LeanQbe.T.Driver",) if not rel.endswith("/Isa.lean") else ()
        for mod, chain in find_transitive_leaks(root, imps, cache, skip_prefixes=skip):
            if (rel, chain[0]) in already_flagged:
                continue
            imp_line = next(
                (imp.line for imp in imps if imp.is_public and imp.module == chain[0]),
                1,
            )
            violations.append(
                Violation(
                    leak_id=leak_id,
                    file=rel,
                    line=imp_line,
                    module=mod,
                    kind="transitive-lemmas",
                    detail="transitive public import path: " + " -> ".join(chain),
                )
            )

    return missing, violations


def run_audit(root: Path, require_isa: bool = False) -> list[LeakGroupReport]:
    """Run all firewall checks (L1-L4) against `root`."""
    cache: dict[Path, list[ImportStmt]] = {}

    l1_files = ["LeanQbe/T/MainLemmas.lean"]
    l2_files = ["LeanQbe/T/Amd64/Targ.lean", "LeanQbe/T/Arm64/Targ.lean"]
    l3_files = ["LeanQbe/T/Amd64/TargLemmas.lean", "LeanQbe/T/Arm64/TargLemmas.lean"]
    l4_files = [
        "Main.lean",
        "MainArm64.lean",
        "LeanQbe/T/Amd64/Isa.lean",
        "LeanQbe/T/Arm64/Isa.lean",
    ]

    # Post-P2A, `{Amd64,Arm64}/TargLemmas.lean` must still publicly import the
    # type-only firewall interface `LeanQbe.T.MainLemmas` (`TargetLayout`,
    # `TargetInit`).
    l3_allowlist = {
        "LeanQbe/T/Amd64/TargLemmas.lean": {"LeanQbe.T.MainLemmas"},
        "LeanQbe/T/Arm64/TargLemmas.lean": {"LeanQbe.T.MainLemmas"},
    }

    l1_missing = [f for f in l1_files if not (root / f).is_file()]
    l2_missing = [f for f in l2_files if not (root / f).is_file()]
    l3_missing = [f for f in l3_files if not (root / f).is_file()]

    l1_viols = check_direct_lemmas(root, "L1", l1_files, {}, cache)
    l2_viols = check_direct_lemmas(root, "L2", l2_files, {}, cache)
    l3_viols = check_direct_lemmas(root, "L3", l3_files, l3_allowlist, cache)
    l4_missing, l4_viols = check_boundary_files(root, "L4", l4_files, cache)

    if require_isa:
        for rel in l4_missing:
            l4_viols.append(
                Violation(
                    leak_id="L4",
                    file=rel,
                    line=0,
                    module="",
                    kind="missing-isa",
                    detail=f"required pure ISA module missing: {rel}",
                )
            )

    return [
        LeakGroupReport(
            leak_id="L1",
            label="MainLemmas (`LeanQbe/T/MainLemmas.lean`)",
            files=l1_files,
            missing_files=l1_missing,
            violations=l1_viols,
        ),
        LeakGroupReport(
            leak_id="L2",
            label="Targ (`{Amd64,Arm64}/Targ.lean`)",
            files=l2_files,
            missing_files=l2_missing,
            violations=l2_viols,
        ),
        LeakGroupReport(
            leak_id="L3",
            label="TargLemmas (`{Amd64,Arm64}/TargLemmas.lean`)",
            files=l3_files,
            missing_files=l3_missing,
            violations=l3_viols,
        ),
        LeakGroupReport(
            leak_id="L4",
            label="Main / Isa executable boundary",
            files=l4_files,
            missing_files=l4_missing,
            violations=l4_viols,
        ),
    ]


def format_human_report(
    groups: list[LeakGroupReport],
    elapsed_ms: float,
    report_only: bool,
) -> str:
    """Render concise human-readable firewall report."""
    active_leaks = [g for g in groups if g.violations]
    total_viols = sum(len(g.violations) for g in groups)
    mode = "report-only" if report_only else "strict"
    lines: list[str] = [
        f"firewall lint ({mode}, {elapsed_ms:.1f}ms): "
        f"{len(active_leaks)}/{len(groups)} leak group(s), "
        f"{total_viols} offending public import(s)"
    ]
    for g in groups:
        status = f"FAIL ({len(g.violations)})" if g.violations else "OK"
        lines.append(f"[{g.leak_id}] {status}: {g.label}")
        if g.missing_files:
            lines.append(
                "  note: pre-P2B absent file(s): " + ", ".join(g.missing_files)
            )
        for v in g.violations:
            loc = f"{v.file}:{v.line}" if v.line > 0 else v.file
            lines.append(f"  - {loc}: {v.detail}")
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for `check_firewall.py`."""
    ap = argparse.ArgumentParser(
        description="Static LeanQbe incrementality-firewall import linter."
    )
    ap.add_argument("--root", default=".", help="Repository root (default: .)")
    ap.add_argument(
        "--report-only",
        action="store_true",
        help="Exit 0 even when firewall leaks are present (pre-P2A reporting).",
    )
    ap.add_argument(
        "--require-isa",
        action="store_true",
        help="Fail if LeanQbe/T/{Amd64,Arm64}/Isa.lean are absent.",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON output.",
    )
    args = ap.parse_args(argv)

    t0 = time.perf_counter()
    root = Path(args.root).resolve()
    groups = run_audit(root, require_isa=args.require_isa)
    elapsed_ms = (time.perf_counter() - t0) * 1000.0

    leak_groups = sum(1 for g in groups if g.violations)
    total_viols = sum(len(g.violations) for g in groups)

    if args.json:
        payload = {
            "mode": "report-only" if args.report_only else "strict",
            "elapsed_ms": round(elapsed_ms, 2),
            "leak_groups": leak_groups,
            "total_violations": total_viols,
            "groups": [
                {
                    "leak_id": g.leak_id,
                    "label": g.label,
                    "files": g.files,
                    "missing_files": g.missing_files,
                    "violations": [
                        {
                            "file": v.file,
                            "line": v.line,
                            "module": v.module,
                            "kind": v.kind,
                            "detail": v.detail,
                        }
                        for v in g.violations
                    ],
                }
                for g in groups
            ],
        }
        print(json.dumps(payload, indent=2))
    else:
        print(format_human_report(groups, elapsed_ms, args.report_only))

    if not args.report_only and total_viols > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
