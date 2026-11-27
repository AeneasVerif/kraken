#!/usr/bin/env python3
"""Static incrementality-firewall linter for LeanQbe module boundaries.

Checks that firewall interface and executable entry modules do not leak proof
lemmas (`*Lemmas*` or `*.Targ`) via `public import`s (Neon Pillar 5 Risk #2):

  - L1 (`MainLemmas`): LeanQbe/T/MainLemmas.lean
  - L2 (`Targ`): LeanQbe/T/{Amd64,Arm64}/Targ.lean
  - L3 (`TargLemmas`): LeanQbe/T/{Amd64,Arm64}/TargLemmas.lean
  - L4 (`Main`/`Isa` boundary): Main.lean, MainArm64.lean,
        LeanQbe/T/{Amd64,Arm64}/Isa.lean
  - L5 (`Param`/`CompileGuard` boundary):
        LeanQbe/T/{Amd64,Arm64}/*Param.lean,
        LeanQbe/T/CompileGuard.lean,
        LeanQbeTest/T/*CompileGuard*.lean

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
SPURIOUS_META_MODS: frozenset[str] = frozenset(
    {
        "LeanQbe.T.PrintCpp",
        "LeanQbe.T.PrintQbe",
        "LeanQbe.T.Legal",
    }
)
DATA_PROOF_ALLOWED_LEMMAS: frozenset[str] = frozenset({"LeanQbe.T.MainLemmas"})
PROOF_TOKEN_RE = re.compile(r"(?:Proof|Lemmas|Audit|Spec)")
DATA_PROOF_SCOPED_PREFIXES: tuple[str, ...] = (
    "LeanQbe.T.Examples.Kissat.FullFidelity",
    "LeanQbe.T.Examples.Kissat.FullM8",
)
DATA_PROOF_EXCLUDED_TOKENS: tuple[str, ...] = (
    "Proof",
    "Lemmas",
    "Audit",
    "Spec",
    "Tactics",
    "Util",
    "Step2S15",
)
TARG_SUFFIX_RE = re.compile(r"\.Targ(?:Lemmas)?$")
PARAM_FILE_RE = re.compile(r"^LeanQbe/T/(Amd64|Arm64)/[^/]+Param\.lean$")
GUARD_LEAF_RE = re.compile(r"^LeanQbeTest/T/[^/]*CompileGuard[^/]*\.lean$")
CERT_MOD_RE = re.compile(r"^LeanQbe\.T\.(?:Amd64|Arm64)\..*Cert.*$")
INL_MOD_RE = re.compile(r"^LeanQbe\.T\.Examples\.Kissat\.Full.*Inl(?:Base|[0-9]+)?$")
GUARD_TARG_PROOF_RE = re.compile(
    r"^LeanQbe\.T\.(?:Amd64|Arm64)\.(?:Targ.*|ScalarTarg|.*Lemmas.*|Kissat.*)$"
)
CERT_ELAB_MODS = frozenset(
    {
        "LeanQbe.T.MainCertElab",
        "LeanQbe.T.MainCertInline",
        "LeanQbe.T.MainCertInlineChunk",
        "LeanQbe.T.MainCertScc",
        "LeanQbe.T.MainCertSlices",
        "LeanQbe.T.MainLinkSplice",
    }
)
ARCH_PREFIXES = ("LeanQbe.T.Amd64.", "LeanQbe.T.Arm64.", "Kraken.X64", "Kraken.AArch64")
ARM64_PREFIXES = ("LeanQbe.T.Arm64.", "Kraken.AArch64")
AMD64_PREFIXES = ("LeanQbe.T.Amd64.", "Kraken.X64")


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
    """Summary of one firewall leak category (L1-L5)."""

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


def discover_data_proof_files(root: Path) -> list[str]:
    """Collect `FullFidelity*` and `FullM8*` AST/Data modules subject to `--data-proof`.

    Excludes proof/spec/tactic/util modules and the backwards-compatible
    `FullFidelityInl.lean` barrel (which intentionally re-exports `FullFidelityInlProof`).
    Base `FullM7*` modules are intentionally left outside this scope.
    """
    kissat_dir = root / "LeanQbe" / "T" / "Examples" / "Kissat"
    if not kissat_dir.is_dir():
        return []
    out: list[str] = []
    for p in sorted(kissat_dir.glob("*.lean")):
        stem = p.stem
        if not (stem.startswith("FullFidelity") or stem.startswith("FullM8")):
            continue
        if stem == "FullFidelityInl":
            continue
        if any(tok in stem for tok in DATA_PROOF_EXCLUDED_TOKENS):
            continue
        out.append(p.relative_to(root).as_posix())
    return out


def _is_proof_module(mod: str) -> bool:
    """Return True if `mod` is a proof/lemmas/audit/spec module outside the allowlist."""
    if mod in DATA_PROOF_ALLOWED_LEMMAS:
        return False
    leaf = mod.rsplit(".", 1)[-1]
    return bool(PROOF_TOKEN_RE.search(leaf))


def check_data_proof_files(
    root: Path,
    rel_files: list[str],
    cache: dict[Path, list[ImportStmt]],
) -> tuple[list[Violation], list[Violation]]:
    """Check `FullFidelity*`/`FullM8*` AST/Data modules for proof & meta leaks.

    Returns `(proof_violations, meta_violations)`:
      - `D1` (`proof_violations`): direct `public`/`meta` imports of `*Proof*`/`*Lemmas*`/
        `*Audit*`/`*Spec*` modules, plus transitive `public import` paths inside
        `FullFidelity*`/`FullM8*` reaching any proof module.
      - `D2` (`meta_violations`): spurious `meta import` of `PrintCpp`, `PrintQbe`,
        or `Legal` on AST/Data modules.
    """
    proof_viols: list[Violation] = []
    meta_viols: list[Violation] = []

    for rel in rel_files:
        path = root / rel
        if not path.is_file():
            continue
        if path not in cache:
            _, imps = parse_imports(path)
            cache[path] = imps
        imps = cache[path]

        direct_flagged: set[str] = set()
        for imp in imps:
            if imp.is_meta and imp.module in SPURIOUS_META_MODS:
                meta_viols.append(
                    Violation(
                        leak_id="D2",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="spurious-meta-import",
                        detail=(
                            f"spurious `meta import {imp.module}` in AST/Data module "
                            "(move `#guard` checks to `LeanQbeTest/T/`)"
                        ),
                    )
                )
            if (imp.is_public or imp.is_meta) and _is_proof_module(imp.module):
                direct_flagged.add(imp.module)
                vis = "public import" if imp.is_public else "meta import"
                proof_viols.append(
                    Violation(
                        leak_id="D1",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="data-to-proof",
                        detail=f"{vis} of `{imp.module}` leaks proof module into AST/Data",
                    )
                )

        # Transitive public-import check scoped to `FullFidelity*`/`FullM8*` so base
        # `FullM7*` modules (e.g. `FullM7Splice`) do not break the gate.
        queue: list[tuple[str, list[str]]] = [
            (imp.module, [imp.module])
            for imp in imps
            if imp.is_public and imp.module.startswith(DATA_PROOF_SCOPED_PREFIXES)
        ]
        visited: set[str] = set()
        while queue:
            mod, chain = queue.pop(0)
            if mod in visited:
                continue
            visited.add(mod)
            if _is_proof_module(mod):
                if chain[0] not in direct_flagged:
                    imp_line = next(
                        (i.line for i in imps if i.is_public and i.module == chain[0]),
                        1,
                    )
                    proof_viols.append(
                        Violation(
                            leak_id="D1",
                            file=rel,
                            line=imp_line,
                            module=mod,
                            kind="transitive-data-to-proof",
                            detail="transitive public import path: " + " -> ".join(chain),
                        )
                    )
                continue
            if not mod.startswith(DATA_PROOF_SCOPED_PREFIXES):
                continue
            mpath = module_to_path(root, mod)
            if mpath is None:
                continue
            if mpath not in cache:
                _, nimps = parse_imports(mpath)
                cache[mpath] = nimps
            for nxt in cache[mpath]:
                if nxt.is_public and nxt.module not in visited:
                    if nxt.module.startswith(DATA_PROOF_SCOPED_PREFIXES) or _is_proof_module(
                        nxt.module
                    ):
                        queue.append((nxt.module, [*chain, nxt.module]))

    return proof_viols, meta_viols


def _load_imports(
    path: Path, cache: dict[Path, list[ImportStmt]]
) -> list[ImportStmt]:
    """Read and cache parsed Lean imports for `path`."""
    if path not in cache:
        _, imps = parse_imports(path)
        cache[path] = imps
    return cache[path]


def _walk_all_imports(
    root: Path,
    start_imports: list[ImportStmt],
    cache: dict[Path, list[ImportStmt]],
    stop_bridge: bool = False,
    stop_cert_bridge: bool = False,
) -> dict[str, tuple[list[str], int]]:
    """Return shortest import chains across all import edges (`public`, private, `meta`).

    When `stop_bridge` is True, traversal does not expand through allowlisted
    metaprogramming bridge modules (`PatchModule`, `Kraken.*`, `*Lemmas*`, or
    transitional `KissatCertCommon`). When `stop_cert_bridge` is True, traversal
    does not expand past transitional `KissatCertCommon` (to be tightened after
    `KissatCertCommon` switches `MainCertInline` -> `MainCertInlineProof`).
    """
    queue: list[tuple[str, list[str], int]] = [
        (imp.module, [imp.module], imp.line) for imp in start_imports
    ]
    reached: dict[str, tuple[list[str], int]] = {}
    while queue:
        mod, chain, first_line = queue.pop(0)
        if mod in reached:
            continue
        reached[mod] = (chain, first_line)
        if stop_cert_bridge and mod == "LeanQbe.T.Examples.Kissat.KissatCertCommon":
            continue
        if stop_bridge and (
            mod
            in {
                "LeanQbe.T.Examples.Kissat.PatchModule",
                "LeanQbe.T.Examples.Kissat.KissatCertCommon",
                "Kraken.Attribute",
                "Kraken.Bedrock2.Notation",
            }
            or "Lemmas" in mod
        ):
            continue
        path = module_to_path(root, mod)
        if path is None or not path.is_file():
            continue
        for nxt in _load_imports(path, cache):
            if nxt.module not in reached:
                queue.append((nxt.module, [*chain, nxt.module], first_line))
    return reached


def _l5_arch_prefixes(rel: str) -> tuple[str, ...]:
    """Return cross-arch module prefixes forbidden for a param or guard file."""
    if "/Amd64/" in rel or rel.endswith("X64.lean"):
        return ARM64_PREFIXES
    if "/Arm64/" in rel or rel.endswith("Arm64.lean"):
        return AMD64_PREFIXES
    return ()


def _is_cert_elab_mod(mod: str) -> bool:
    """Return True if `mod` is an elaboration/chunk/splice cert module."""
    return mod in CERT_ELAB_MODS or mod.startswith("LeanQbe.T.MainCertSlices")


def _discover_l5_files(root: Path) -> tuple[list[str], list[str], list[str]]:
    """Collect existing L5 parametric, pure guard, and guard-leaf files under `root`."""
    param_files: list[str] = []
    for arch in ("Amd64", "Arm64"):
        d = root / "LeanQbe" / "T" / arch
        if d.is_dir():
            for p in sorted(d.glob("*Param.lean")):
                rel = p.relative_to(root).as_posix()
                if PARAM_FILE_RE.match(rel):
                    param_files.append(rel)

    guard_core = ["LeanQbe/T/CompileGuard.lean"] if (root / "LeanQbe/T/CompileGuard.lean").is_file() else []

    guard_leaves: list[str] = []
    test_dir = root / "LeanQbeTest" / "T"
    if test_dir.is_dir():
        for p in sorted(test_dir.glob("*CompileGuard*.lean")):
            rel = p.relative_to(root).as_posix()
            if GUARD_LEAF_RE.match(rel):
                guard_leaves.append(rel)
    return param_files, guard_core, guard_leaves


def _flag_chain_violations(
    rel: str,
    reached: dict[str, tuple[list[str], int]],
    predicate,
    kind: str,
    reason: str,
) -> list[Violation]:
    """Build deterministic violations for every reached module matching `predicate`."""
    out: list[Violation] = []
    for mod in sorted(reached):
        if not predicate(mod):
            continue
        chain, line = reached[mod]
        out.append(
            Violation(
                leak_id="L5",
                file=rel,
                line=line,
                module=mod,
                kind=kind,
                detail=f"{reason}: {' -> '.join(chain)}",
            )
        )
    return out


def check_l5_param_and_guards(
    root: Path, cache: dict[Path, list[ImportStmt]]
) -> tuple[list[str], list[Violation]]:
    """Verify Tier-1 `*Param.lean`, `CompileGuard.lean`, and Tier-2 `*CompileGuard*.lean`."""
    param_files, guard_core, guard_leaves = _discover_l5_files(root)
    violations: list[Violation] = []

    for rel in param_files:
        imps = _load_imports(root / rel, cache)
        reached = _walk_all_imports(root, imps, cache)
        cert_unbridged = _walk_all_imports(root, imps, cache, stop_cert_bridge=True)
        unbridged = _walk_all_imports(root, imps, cache, stop_bridge=True)
        bad_arch = _l5_arch_prefixes(rel)

        violations.extend(
            _flag_chain_violations(
                rel,
                cert_unbridged,
                lambda m: bool(CERT_MOD_RE.match(m)) or _is_cert_elab_mod(m),
                "param-cert-leak",
                "Tier-1 *Param module pulls cert/elab module",
            )
        )
        violations.extend(
            _flag_chain_violations(
                rel,
                reached,
                lambda m: bool(CERT_MOD_RE.match(m))
                or m.startswith("LeanQbe.T.MainCertSlices")
                or m in {"LeanQbe.T.MainCertInlineChunk", "LeanQbe.T.MainCertScc"},
                "param-cert-leak",
                "Tier-1 *Param module pulls cert/chunk/slice module",
            )
        )
        violations.extend(
            _flag_chain_violations(
                rel,
                reached,
                lambda m: bool(INL_MOD_RE.match(m)),
                "param-inl-leak",
                "Tier-1 *Param module pulls materialized *Inl* AST module",
            )
        )
        if bad_arch:
            violations.extend(
                _flag_chain_violations(
                    rel,
                    reached,
                    lambda m, p=bad_arch: m.startswith(p),
                    "param-cross-arch",
                    "Tier-1 *Param module pulls opposite-arch module",
                )
            )
        violations.extend(
            _flag_chain_violations(
                rel,
                unbridged,
                lambda m: m == "Lean",
                "param-lean-meta",
                "Tier-1 *Param module pulls un-allowlisted `Lean` meta module",
            )
        )

    for rel in guard_core:
        imps = _load_imports(root / rel, cache)
        reached = _walk_all_imports(root, imps, cache)
        forbidden = (
            lambda m: "Lemmas" in m
            or "Proof" in m
            or "Cert" in m
            or m == "LeanQbe.T.MainInline"
            or m.startswith("LeanQbe.T.MainCert")
            or bool(TARG_SUFFIX_RE.search(m))
            or m == "Lean"
            or m.startswith(ARCH_PREFIXES)
        )
        violations.extend(
            _flag_chain_violations(
                rel,
                reached,
                forbidden,
                "compile-guard-core-leak",
                "pure `CompileGuard` module pulls forbidden proof/target/meta module",
            )
        )

    for rel in guard_leaves:
        imps = _load_imports(root / rel, cache)
        bad_arch = _l5_arch_prefixes(rel)
        for imp in imps:
            if imp.is_public:
                violations.append(
                    Violation(
                        leak_id="L5",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="guard-public-import",
                        detail=f"Tier-2 guard leaf must use `meta import` (not `public import {imp.module}`)",
                    )
                )
            if (
                "Lemmas" in imp.module
                or "Proof" in imp.module
                or "Cert" in imp.module
                or bool(TARG_SUFFIX_RE.search(imp.module))
                or imp.module == "LeanQbe.T.MainInline"
                or imp.module.startswith("LeanQbe.T.MainCert")
                or imp.module == "Lean"
            ):
                violations.append(
                    Violation(
                        leak_id="L5",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="guard-direct-forbidden",
                        detail=f"Tier-2 guard leaf directly imports forbidden module `{imp.module}`",
                    )
                )

        reached = _walk_all_imports(root, imps, cache)
        unbridged = _walk_all_imports(root, imps, cache, stop_bridge=True)
        violations.extend(
            _flag_chain_violations(
                rel,
                reached,
                lambda m: (
                    "Cert" in m
                    or _is_cert_elab_mod(m)
                    or bool(INL_MOD_RE.match(m))
                    or bool(GUARD_TARG_PROOF_RE.match(m))
                ),
                "guard-transitive-leak",
                "Tier-2 guard leaf transitively pulls forbidden cert/inl/target-proof module",
            )
        )
        if bad_arch:
            violations.extend(
                _flag_chain_violations(
                    rel,
                    reached,
                    lambda m, p=bad_arch: m.startswith(p),
                    "guard-cross-arch",
                    "Tier-2 guard leaf pulls opposite-arch module",
                )
            )
        violations.extend(
            _flag_chain_violations(
                rel,
                unbridged,
                lambda m: m == "Lean",
                "guard-lean-meta",
                "Tier-2 guard leaf pulls un-allowlisted `Lean` meta module",
            )
        )

    return [*param_files, *guard_core, *guard_leaves], violations


def run_audit(
    root: Path,
    require_isa: bool = False,
    data_proof: bool = False,
) -> list[LeakGroupReport]:
    """Run all firewall checks (L1-L5, plus optional D1-D2 `--data-proof`) against `root`."""
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

    l5_files, l5_viols = check_l5_param_and_guards(root, cache)

    reports = [
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
        LeakGroupReport(
            leak_id="L5",
            label="Parametric / CompileGuard firewall",
            files=l5_files,
            missing_files=[],
            violations=l5_viols,
        ),
    ]
    if data_proof:
        dp_files = discover_data_proof_files(root)
        d1_viols, d2_viols = check_data_proof_files(root, dp_files, cache)
        reports.extend(
            [
                LeakGroupReport(
                    leak_id="D1",
                    label="AST/Data -> Proof firewall (`FullFidelity*`/`FullM8*`)",
                    files=dp_files,
                    violations=d1_viols,
                ),
                LeakGroupReport(
                    leak_id="D2",
                    label=(
                        "Spurious printer/legal `meta import` firewall "
                        "(`FullFidelity*`/`FullM8*`)"
                    ),
                    files=dp_files,
                    violations=d2_viols,
                ),
            ]
        )
    return reports


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
        "--data-proof",
        action="store_true",
        help=(
            "Enforce AST/Data -> Proof and spurious printer/legal `meta import` "
            "firewalls on `FullFidelity*`/`FullM8*` AST/Data modules."
        ),
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON output.",
    )
    args = ap.parse_args(argv)

    t0 = time.perf_counter()
    root = Path(args.root).resolve()
    groups = run_audit(root, require_isa=args.require_isa, data_proof=args.data_proof)
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
