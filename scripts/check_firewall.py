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
import collections
import json
import re
import sys
import time
from collections.abc import Mapping, Set as AbstractSet
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from lean_imports import (
    ANY_ATTR_RE,
    BARRELS,
    DECL_RE,
    ImportStmt,
    list_lean_files,
    module_to_path,
    parse_imports,
    rel_path_to_mod,
    scan_import_all_sites,
    strip_lean_code,
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
    "LeanQbe.T.Examples.Kissat.Src.",
)
DATA_PROOF_EXCLUDED_TOKENS: tuple[str, ...] = (
    "Proof",
    "Lemmas",
    "Audit",
    "Spec",
    "Tactics",
    "Util",
)
TARG_SUFFIX_RE = re.compile(r"\.Targ(?:Lemmas)?$")
PARAM_FILE_RE = re.compile(r"^LeanQbe/T/(Amd64|Arm64)/[^/]+Param\.lean$")
GUARD_LEAF_RE = re.compile(r"^LeanQbeTest/T/[^/]*CompileGuard[^/]*\.lean$")
CERT_MOD_RE = re.compile(r"^LeanQbe\.T\.(?:Amd64|Arm64)\..*Cert.*$")
INL_MOD_RE = re.compile(
    r"^LeanQbe\.T\.Examples\.Kissat\.(?:Full.*Inl(?:Base|[0-9]+)?|Build\.Inl\..*)$"
)
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
AMD64_PREFIXES = (
    "LeanQbe.T.Amd64.",
    "LeanQbe.T.Examples.Kissat.Build.Amd64.",
    "LeanQbe.T.Examples.Kissat.Build.Oracle.Amd64.",
    "Kraken.X64",
)
ARM64_PREFIXES = (
    "LeanQbe.T.Arm64.",
    "LeanQbe.T.Examples.Kissat.Build.Arm64.",
    "LeanQbe.T.Examples.Kissat.Build.Oracle.Arm64.",
    "Kraken.AArch64",
)
ARCH_PREFIXES = (*AMD64_PREFIXES, *ARM64_PREFIXES)

PURITY_REF_PATH_RE = re.compile(r"(?:^|/)Kissat[^/]*/Ref/.*\.lean$")
PURITY_SPEC_PATH_RE = re.compile(
    r"(?:^|/)Kissat[^/]*/(?:[^/]+/)*(?:Spec/.*|Proof/Spec/.*|Proof/[^/]+/Spec[^/]*)\.lean$"
)
PURITY_FORBIDDEN_DECL_RE = re.compile(
    r"^(?:(?:public|private|protected|noncomputable|unsafe|partial|local|"
    r"scoped|meta|nonrec)\s+)*"
    r"(theorem|lemma|axiom|elab|elab_rules|macro|macro_rules|syntax|declare_syntax_cat)\b"
)
PURITY_REF_FORBIDDEN_IMP_RE = re.compile(
    r"(?:^|\.)(?:Kraken|Frontend\.C0|T\.Logic|Src|Spec|Proof)(?:\.|$)"
)
PURITY_SPEC_DEPS_RE = re.compile(
    r"^(?:(?:public|private|protected|noncomputable|unsafe|partial|local|"
    r"scoped|meta|nonrec)\s+)*(?:def|abbrev)\s+deps\b"
)
PURITY_SPEC_FORBIDDEN_EXACT: frozenset[str] = frozenset(
    {
        "LeanQbe.T.Logic.C0Step",
        "LeanQbe.T.Logic.C0HeadStep",
        "LeanQbe.T.Logic.ControlComb",
        "LeanQbe.T.Logic.SlabChain",
        "Kraken.SeparationTactics",
    }
)
PURITY_SPEC_SHARED_LEAVES: frozenset[str] = frozenset(
    {"Core", "Layout", "HdrView", "Header", "Inv", "Solver"}
)
PURITY_SPEC_RAW_IDX_RE = re.compile(r"\b(?:ws'?|kbuf'?|hdr)\[[0-9]+\]\?")
PURITY_SPEC_LEGACY_RE = re.compile(
    r"(?:SafetySlice|m6HdrW2aSpec|readModelFromWork|[Ss]tep13|(?:^|_)s13|S13)"
)
PURITY_SPEC_FIELD_START_RE = re.compile(r"(?:^|[\s{,])(pre|post)\s*:=", re.MULTILINE)
PURITY_SPEC_NEXT_FIELD_RE = re.compile(r"^[ \t]*(?:extFrame|pre|mem|post|postMem)\s*:=")
PURITY_SPEC_TOP_END_RE = re.compile(
    r"^(?:@\[|(?:public|private|protected|noncomputable|unsafe|partial|local|"
    r"scoped|meta|nonrec)?\s*(?:def|abbrev|structure|inductive|class|end|section|namespace)\b)"
)

MODSYS_ROOTS: tuple[str, ...] = ("LeanQbe", "LeanQbeTest", "LeanQbeBootstrap0Test")
M1_DIRECT_EXEC_ROOTS: tuple[str, ...] = (
    "LeanQbe/T/MainFlat.lean",
    "LeanQbe/T/Main.lean",
    "LeanQbe/T/InlinePlanSeg.lean",
    "LeanQbe/T/Amd64/Isa.lean",
    "LeanQbe/T/Arm64/Isa.lean",
    "LeanQbe/T/Frontend/C0/Elab.lean",
)
M1_EXTRA_CERT_ELAB_FILES: tuple[str, ...] = (
    "LeanQbe/T/MainCertSegStaged.lean",
    "LeanQbe/T/MainCertInline.lean",
    "LeanQbe/T/MainCertInlineChunk.lean",
    "LeanQbe/T/MainCertScc.lean",
)
M2_SCOPE_RE = re.compile(
    r"^(?:LeanQbe/(?:.*/)?Build/(?:Inl|Amd64|Arm64)/[^/]+\.lean"
    r"|LeanQbe/T/(?:Amd64|Arm64)/[^/]*Cert[^/]*\.lean)$"
)
M3_ALLOWLIST_EXACT_STEMS: frozenset[str] = frozenset(
    {
        "MainCertInline",
        "MainCertInlineChunk",
        "MainCertScc",
        "MainCertSegStaged",
        "MainCertFlatDecode",
    }
)
M4_PROOF_EXACT_MODS: frozenset[str] = frozenset(
    {
        "LeanQbe.T.Logic.ControlComb",
        "Kraken.SeparationTactics",
    }
)
M4_PROOF_PREFIXES: tuple[str, ...] = (
    "LeanQbe.T.Logic.C0Step",
    "LeanQbe.T.Logic.C0HeadStep",
    "LeanQbe.T.Logic.ProofKit",
)


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
    """Summary of one firewall leak category (L1-L5, D1-D2, P-Ref/P-Spec, M1-M6)."""

    leak_id: str
    label: str
    files: list[str]
    missing_files: list[str] = field(default_factory=list)
    violations: list[Violation] = field(default_factory=list)
    report_only: bool = False


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
    """Collect canonical `Kissat/Src/*.lean` AST/Data modules subject to `--data-proof`."""
    src_dir = root / "LeanQbe" / "T" / "Examples" / "Kissat" / "Src"
    if not src_dir.is_dir():
        return []
    out: list[str] = []
    for p in sorted(src_dir.glob("*.lean")):
        stem = p.stem
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
    """Check `Kissat/Src/*.lean` AST/Data modules for proof & meta leaks.

    Returns `(proof_violations, meta_violations)`:
      - `D1` (`proof_violations`): direct `public`/`meta` imports of `*Proof*`/`*Lemmas*`/
        `*Audit*`/`*Spec*` modules, plus transitive `public import` paths inside
        `Kissat/Src/*` reaching any proof module.
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

        # Transitive public-import check scoped to `Kissat/Src/*` AST/Data modules.
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
) -> dict[str, tuple[list[str], int]]:
    """Return shortest import chains across all import edges (`public`, private, `meta`).

    When `stop_bridge` is True, traversal does not expand through allowlisted
    metaprogramming bridge modules (`Kraken.*`, `*Lemmas*`, or proof kits).
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
        if stop_bridge and (
            mod
            in {
                "LeanQbe.T.Logic.C0Grind",
                "LeanQbe.T.Logic.ProofKit",
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
        unbridged = _walk_all_imports(root, imps, cache, stop_bridge=True)
        bad_arch = _l5_arch_prefixes(rel)

        violations.extend(
            _flag_chain_violations(
                rel,
                reached,
                lambda m: bool(CERT_MOD_RE.match(m)) or _is_cert_elab_mod(m),
                "param-cert-leak",
                "Tier-1 *Param module pulls cert/elab module",
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


def _walk_lean_files(root: Path, path_re: re.Pattern[str]) -> list[str]:
    """Collect relative `.lean` paths under `root` matching `path_re` (skipping `.lake`/`.git`)."""
    out: list[str] = []
    for p in sorted(root.rglob("*.lean")):
        if ".lake" in p.parts or ".git" in p.parts:
            continue
        rel = p.relative_to(root).as_posix()
        if path_re.search(rel):
            out.append(rel)
    return out


def discover_purity_ref_files(root: Path) -> list[str]:
    """Collect `**/Kissat*/Ref/*.lean` files subject to Rule `P-Ref`."""
    return _walk_lean_files(root, PURITY_REF_PATH_RE)


def discover_purity_spec_files(root: Path) -> list[str]:
    """Collect `**/Kissat*/Spec/*.lean` and pre-W8 `Proof/Spec*` files subject to Rule `P-Spec`."""
    return _walk_lean_files(root, PURITY_SPEC_PATH_RE)


def check_purity_ref_files(
    root: Path,
    rel_files: list[str],
    cache: dict[Path, list[ImportStmt]],
) -> list[Violation]:
    """Enforce Rule `P-Ref` (`0` proofs/tactics/`meta import`, `0` C0/Kraken/Spec/Proof imports)."""
    viols: list[Violation] = []
    for rel in rel_files:
        path = root / rel
        if not path.is_file():
            continue
        imps = _load_imports(path, cache)
        for imp in imps:
            if imp.is_meta:
                viols.append(
                    Violation(
                        leak_id="P-Ref",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="ref-meta-import",
                        detail=f"forbidden `meta import {imp.module}` in pure `Ref/` module",
                    )
                )
            if PURITY_REF_FORBIDDEN_IMP_RE.search(imp.module):
                viols.append(
                    Violation(
                        leak_id="P-Ref",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="ref-forbidden-import",
                        detail=(
                            f"forbidden import `{imp.module}` in `Ref/` "
                            "(no `Kraken`, `Frontend.C0`, `T.Logic`, `Src`, `Spec`, `Proof`)"
                        ),
                    )
                )
        cleaned = strip_lean_code(path.read_text(encoding="utf-8"))
        for lineno, raw_line in enumerate(cleaned.splitlines(), start=1):
            code = ANY_ATTR_RE.sub("", raw_line).strip()
            if not code:
                continue
            m = PURITY_FORBIDDEN_DECL_RE.match(code)
            if m:
                viols.append(
                    Violation(
                        leak_id="P-Ref",
                        file=rel,
                        line=lineno,
                        module="",
                        kind="ref-forbidden-decl",
                        detail=f"forbidden `{m.group(1)}` declaration in pure `Ref/` module",
                    )
                )
    return viols


def _is_forbidden_spec_import(mod: str) -> tuple[str, str] | None:
    """Return `(kind, detail)` if `mod` violates Rule `P-Spec` import restrictions."""
    if mod in PURITY_SPEC_FORBIDDEN_EXACT:
        return ("spec-forbidden-import", f"forbidden import `{mod}` in pure `Spec/` module")
    m_spec = re.search(r"(?:^|\.)(?:Proof\.)?Spec\.([^.]+)$", mod)
    if m_spec:
        leaf = m_spec.group(1)
        if leaf not in PURITY_SPEC_SHARED_LEAVES:
            return (
                "spec-cross-spec-import",
                f"cross-subsystem `Spec` import `{mod}` (only shared `Spec.{{Core,Layout,HdrView,Header,Inv,Solver}}` allowed)",
            )
        return None
    if re.search(r"(?:^|\.)Proof(?:\.|$)", mod):
        return ("spec-proof-import", f"forbidden `Proof.*` import `{mod}` in pure `Spec/` module")
    return None


def _strip_outer_parens(expr: str) -> str:
    """Strip a single balanced outer `(...)` pair if it wraps the whole expression."""
    s = expr.strip()
    while len(s) >= 2 and s[0] == "(" and s[-1] == ")":
        depth = 0
        wraps_all = True
        for i, ch in enumerate(s):
            if ch == "(":
                depth += 1
            elif ch == ")":
                depth -= 1
                if depth == 0 and i < len(s) - 1:
                    wraps_all = False
                    break
        if wraps_all and depth == 0:
            s = s[1:-1].strip()
        else:
            break
    return s


def _count_pre_post_conjuncts(cleaned: str) -> list[tuple[int, str, int]]:
    """Return `(line, field_name, conjunct_count)` for every `pre`/`post` body with > 12 conjuncts."""
    hits: list[tuple[int, str, int]] = []
    n = len(cleaned)
    for m in PURITY_SPEC_FIELD_START_RE.finditer(cleaned):
        field_name = m.group(1)
        pos = m.end()
        start_line = cleaned[: m.start(1)].count("\n") + 1
        dp = db = dc = 0
        end = pos
        while end < n:
            ch = cleaned[end]
            if ch == "(":
                dp += 1
            elif ch == ")":
                if dp == 0:
                    break
                dp -= 1
            elif ch == "[":
                db += 1
            elif ch == "]":
                if db == 0:
                    break
                db -= 1
            elif ch == "{":
                dc += 1
            elif ch == "}":
                if dc == 0:
                    break
                dc -= 1
            elif ch == "," and dp == 0 and db == 0 and dc == 0:
                break
            elif ch == "\n" and dp == 0 and db == 0 and dc == 0:
                rest = cleaned[end + 1 :]
                if PURITY_SPEC_NEXT_FIELD_RE.match(rest) or PURITY_SPEC_TOP_END_RE.match(rest):
                    break
            end += 1
        body = cleaned[pos:end].strip()
        if "=>" in body:
            # Advance past top-level `fun ... =>` header if present before outer grouping.
            p_dp = p_db = p_dc = 0
            i = 0
            while i + 1 < len(body):
                c = body[i]
                if c == "(":
                    p_dp += 1
                elif c == ")":
                    p_dp = max(0, p_dp - 1)
                elif c == "[":
                    p_db += 1
                elif c == "]":
                    p_db = max(0, p_db - 1)
                elif c == "{":
                    p_dc += 1
                elif c == "}":
                    p_dc = max(0, p_dc - 1)
                elif body[i : i + 2] == "=>" and p_dp == 0 and p_db == 0 and p_dc == 0:
                    body = body[i + 2 :].strip()
                    break
                i += 1
        body = _strip_outer_parens(body)
        if not body:
            continue
        p_dp = p_db = p_dc = 0
        ands = 0
        i = 0
        blen = len(body)
        while i < blen:
            c = body[i]
            if c == "(":
                p_dp += 1
            elif c == ")":
                p_dp = max(0, p_dp - 1)
            elif c == "[":
                p_db += 1
            elif c == "]":
                p_db = max(0, p_db - 1)
            elif c == "{":
                p_dc += 1
            elif c == "}":
                p_dc = max(0, p_dc - 1)
            elif p_dp == 0 and p_db == 0 and p_dc == 0:
                if c == "∧":
                    ands += 1
                elif body[i : i + 2] == "/\\":
                    ands += 1
                    i += 1
            i += 1
        conjuncts = ands + 1
        if conjuncts > 12:
            hits.append((start_line, field_name, conjuncts))
    return hits


def check_purity_spec_files(
    root: Path,
    rel_files: list[str],
    cache: dict[Path, list[ImportStmt]],
) -> list[Violation]:
    """Enforce Rule `P-Spec` on `Kissat*/Spec/*` and pre-W8 `Proof/*/Spec*` modules."""
    viols: list[Violation] = []
    for rel in rel_files:
        path = root / rel
        if not path.is_file():
            continue
        imps = _load_imports(path, cache)
        for imp in imps:
            if imp.is_meta:
                viols.append(
                    Violation(
                        leak_id="P-Spec",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="spec-meta-import",
                        detail=f"forbidden `meta import {imp.module}` in pure `Spec/` module",
                    )
                )
            if imp.is_all:
                viols.append(
                    Violation(
                        leak_id="P-Spec",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="spec-import-all",
                        detail=f"forbidden `import all {imp.module}` in pure `Spec/` module",
                    )
                )
            bad = _is_forbidden_spec_import(imp.module)
            if bad is not None:
                kind, detail = bad
                viols.append(
                    Violation(
                        leak_id="P-Spec",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind=kind,
                        detail=detail,
                    )
                )

        cleaned = strip_lean_code(path.read_text(encoding="utf-8"))
        for lineno, raw_line in enumerate(cleaned.splitlines(), start=1):
            code = ANY_ATTR_RE.sub("", raw_line).strip()
            if not code:
                continue
            m_decl = PURITY_FORBIDDEN_DECL_RE.match(code)
            if m_decl:
                viols.append(
                    Violation(
                        leak_id="P-Spec",
                        file=rel,
                        line=lineno,
                        module="",
                        kind="spec-forbidden-decl",
                        detail=f"forbidden `{m_decl.group(1)}` declaration in pure `Spec/` module",
                    )
                )
            if PURITY_SPEC_DEPS_RE.match(code):
                viols.append(
                    Violation(
                        leak_id="P-Spec",
                        file=rel,
                        line=lineno,
                        module="",
                        kind="spec-deps-decl",
                        detail="forbidden `deps` declaration in `Spec/` (move to `Proof/<Sub>/Cert.lean`)",
                    )
                )
            m_d = DECL_RE.match(code)
            if m_d and m_d.group(2) and PURITY_SPEC_LEGACY_RE.search(m_d.group(2)):
                viols.append(
                    Violation(
                        leak_id="P-Spec",
                        file=rel,
                        line=lineno,
                        module="",
                        kind="spec-legacy-ident",
                        detail=f"legacy identifier in declaration `{m_d.group(2)}`",
                    )
                )
            m_idx = PURITY_SPEC_RAW_IDX_RE.search(code)
            if m_idx:
                viols.append(
                    Violation(
                        leak_id="P-Spec",
                        file=rel,
                        line=lineno,
                        module="",
                        kind="spec-raw-index",
                        detail=f"raw positional header/array index `{m_idx.group(0)}` (use `HdrView`/`HdrWordField`)",
                    )
                )
        for lineno, fname, cnt in _count_pre_post_conjuncts(cleaned):
            viols.append(
                Violation(
                    leak_id="P-Spec",
                    file=rel,
                    line=lineno,
                    module="",
                    kind="spec-conjunct-cap",
                    detail=f"`{fname}` body has {cnt} > 12 conjuncts (factor into `<Fn>Pre`/`<Fn>Post`)",
                )
            )
    return viols


def _discover_modsys_files(
    root: Path, roots: tuple[str, ...] = MODSYS_ROOTS
) -> list[str]:
    """List repo-relative `.lean` paths under `roots`, excluding `.lake`/`.git`/`Kraken`."""
    present = tuple(r for r in roots if (root / r).is_dir())
    if not present:
        return []
    rels = list_lean_files(
        root,
        *present,
        excludes=("Kraken", "bv_decide_qbe", "archive", ".lake", ".git"),
    )
    return [
        r.as_posix()
        for r in rels
        if ".lake" not in r.parts and ".git" not in r.parts
    ]


def _is_m1_proof_module(mod: str) -> bool:
    """Return True if `mod` is a proof/lemma/check/tactic module banned from `metaTransTrace`."""
    leaf = mod.rsplit(".", 1)[-1]
    if "Lemmas" in mod or "Check" in leaf:
        return True
    if ".Proof." in mod or mod.endswith(".Proof"):
        return True
    if mod == "Kraken.SeparationTactics":
        return True
    if mod.startswith(("LeanQbe.T.Logic.C0Step", "LeanQbe.T.Logic.ProofKit")):
        return True
    return False


def _walk_m1_shortest_proof_hits(
    root: Path,
    start_imports: list[ImportStmt],
    cache: dict[Path, list[ImportStmt]],
) -> list[tuple[str, list[str], int]]:
    """BFS over ALL import edges (public, private, meta, all) stopping at proof hits."""
    q: collections.deque[tuple[str, list[str], int]] = collections.deque(
        (imp.module, [imp.module], imp.line) for imp in start_imports
    )
    visited: set[str] = set()
    hits: list[tuple[str, list[str], int]] = []
    while q:
        mod, chain, first_line = q.popleft()
        if mod in visited:
            continue
        visited.add(mod)
        if _is_m1_proof_module(mod):
            hits.append((mod, chain, first_line))
            continue
        path = module_to_path(root, mod)
        if path is None or not path.is_file():
            continue
        for nxt in _load_imports(path, cache):
            if nxt.module not in visited:
                q.append((nxt.module, [*chain, nxt.module], first_line))
    return hits


def check_m1_exec_meta_firewall(
    root: Path,
    cache: dict[Path, list[ImportStmt]],
) -> tuple[list[str], list[Violation]]:
    """M1: Executable-root zero-proof `metaTransTrace` firewall (walks private imports!)."""
    exec_files = [rel for rel in M1_DIRECT_EXEC_ROOTS if (root / rel).is_file()]
    cert_elab_set: set[str] = set()
    t_dir = root / "LeanQbe" / "T"
    if t_dir.is_dir():
        for p in sorted(t_dir.rglob("*Cert*Elab*.lean")):
            if ".lake" in p.parts or ".git" in p.parts:
                continue
            cert_elab_set.add(p.relative_to(root).as_posix())
    for rel in M1_EXTRA_CERT_ELAB_FILES:
        if (root / rel).is_file():
            cert_elab_set.add(rel)
    cert_elab_files = sorted(cert_elab_set)

    violations: list[Violation] = []
    for rel in exec_files:
        imps = _load_imports(root / rel, cache)
        for mod, chain, line in _walk_m1_shortest_proof_hits(root, imps, cache):
            violations.append(
                Violation(
                    leak_id="M1",
                    file=rel,
                    line=line,
                    module=mod,
                    kind="m1-exec-proof-leak",
                    detail=(
                        "executable root reaches proof module via metaTransTrace "
                        "(including private imports): " + " -> ".join(chain)
                    ),
                )
            )

    for rel in cert_elab_files:
        imps = _load_imports(root / rel, cache)
        meta_imps = [imp for imp in imps if imp.is_meta]
        for mod, chain, line in _walk_m1_shortest_proof_hits(root, meta_imps, cache):
            violations.append(
                Violation(
                    leak_id="M1",
                    file=rel,
                    line=line,
                    module=mod,
                    kind="m1-cert-elab-meta-proof-leak",
                    detail=(
                        "cert elaborator `meta import` reaches proof module via "
                        "metaTransTrace: " + " -> ".join(chain)
                    ),
                )
            )

    return [*exec_files, *cert_elab_files], violations


def check_m2_build_cert_imports(
    root: Path,
    all_files: list[str],
    cache: dict[Path, list[ImportStmt]],
) -> tuple[list[str], list[Violation]]:
    """M2: `Build/*` & `*Cert*` elaborator (`import *Elab`) and target (`meta import *.Isa`) firewall."""
    scoped = [rel for rel in all_files if M2_SCOPE_RE.match(rel)]
    violations: list[Violation] = []
    for rel in scoped:
        imps = _load_imports(root / rel, cache)
        for imp in imps:
            if not imp.is_meta:
                continue
            leaf = imp.module.rsplit(".", 1)[-1]
            if leaf.endswith("Elab"):
                violations.append(
                    Violation(
                        leak_id="M2",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="m2-meta-elab-import",
                        detail=(
                            f"forbidden `meta import {imp.module}` in Build/Cert module "
                            f"(use plain private `import {imp.module}`)"
                        ),
                    )
                )
            elif imp.module.endswith(".Targ"):
                violations.append(
                    Violation(
                        leak_id="M2",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="m2-meta-targ-import",
                        detail=(
                            f"forbidden `meta import {imp.module}` walks Targ private "
                            "proof imports (use `meta import *.Isa`)"
                        ),
                    )
                )
    return scoped, violations


def _is_m3_allowlisted(rel: str) -> bool:
    """Return True if `rel` is allowlisted to use `public meta import`."""
    if rel.startswith(("LeanQbeTest/", "LeanQbeBootstrap0Test/")):
        return False
    if rel.endswith("/Src/Header.lean") or rel == "Src/Header.lean":
        return False
    if "/Proof/" in f"/{rel}":
        return False
    stem = Path(rel).stem
    if "Lemmas" in stem or stem.startswith(("Wp", "Helpers")):
        return False
    if stem in M3_ALLOWLIST_EXACT_STEMS:
        return True
    if stem.endswith(("Elab", "Attr", "Syntax")) or stem.startswith("Notation"):
        return True
    if "Tactics" in stem or "Splice" in stem:
        return True
    return False


def check_m3_public_meta_allowlist(
    root: Path,
    all_files: list[str],
    cache: dict[Path, list[ImportStmt]],
) -> list[Violation]:
    """M3: Ban `public meta import` outside explicitly allowlisted meta/elab/syntax modules."""
    violations: list[Violation] = []
    for rel in all_files:
        if _is_m3_allowlisted(rel):
            continue
        imps = _load_imports(root / rel, cache)
        for imp in imps:
            if imp.is_public and imp.is_meta:
                violations.append(
                    Violation(
                        leak_id="M3",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="m3-public-meta-import",
                        detail=(
                            f"forbidden `public meta import {imp.module}` outside "
                            "allowlisted meta/elab modules"
                        ),
                    )
                )
    return violations


def _is_m4_proof_tactic_module(mod: str) -> bool:
    """Return True if `mod` is a proof-automation/tactic module banned from `public import`."""
    if mod in M4_PROOF_EXACT_MODS:
        return True
    if mod.endswith(".Proof.Lib.ContractLemmas"):
        return True
    if not mod.endswith("Rules") and mod.startswith(M4_PROOF_PREFIXES):
        return True
    leaf = mod.rsplit(".", 1)[-1]
    if "Tactics" in leaf:
        return True
    return False


def check_m4_proof_public_imports(
    root: Path,
    all_files: list[str],
    cache: dict[Path, list[ImportStmt]],
) -> tuple[list[str], list[Violation]]:
    """M4: Ban `public import` of pure tactic/proof-automation modules in `Proof/` & `*Lemmas*`."""
    scoped = [
        rel
        for rel in all_files
        if rel.startswith("LeanQbe/")
        and ("/Proof/" in f"/{rel}" or "Lemmas" in Path(rel).stem)
    ]
    violations: list[Violation] = []
    for rel in scoped:
        imps = _load_imports(root / rel, cache)
        for imp in imps:
            if imp.is_public and _is_m4_proof_tactic_module(imp.module):
                violations.append(
                    Violation(
                        leak_id="M4",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="m4-proof-public-import",
                        detail=(
                            f"proof-only module `{imp.module}` must use private "
                            "`import`, not `public import`"
                        ),
                    )
                )
    return scoped, violations


def check_m5_import_all_repo_wide(
    root: Path,
    allowlist: AbstractSet[str] | Mapping[str, AbstractSet[str]] | None = None,
) -> list[Violation]:
    """M5: Repo-wide zero `import all` rule across `LeanQbe*` / `LeanQbe*Test`."""
    violations: list[Violation] = []
    for rel, imp in scan_import_all_sites(root, roots=MODSYS_ROOTS, allowlist=allowlist):
        is_bad = imp.is_public or imp.module.startswith("LeanQbe")
        kind = "bad-import-all" if is_bad else "import-all"
        detail = (
            f"forbidden `{'public ' if imp.is_public else ''}import all {imp.module}`"
            + (" (BAD_IMPORT_ALL)" if is_bad else " (M5 repo-wide ban)")
        )
        violations.append(
            Violation(
                leak_id="M5",
                file=rel,
                line=imp.line,
                module=imp.module,
                kind=kind,
                detail=detail,
            )
        )
    return violations


def check_m6_hub_and_leaf_tests(
    root: Path,
    all_files: list[str],
    cache: dict[Path, list[ImportStmt]],
) -> list[Violation]:
    """M6: Ban `*Hub` imports in library/test modules and `public [meta] import` in leaf tests."""
    rdep_counts: dict[str, int] = collections.defaultdict(int)
    file_imps: list[tuple[str, str, list[ImportStmt]]] = []
    for rel in all_files:
        mod = rel_path_to_mod(Path(rel))
        imps = _load_imports(root / rel, cache)
        file_imps.append((rel, mod, imps))
        if mod in BARRELS:
            continue
        for imp in imps:
            rdep_counts[imp.module] += 1

    violations: list[Violation] = []
    for rel, mod, imps in file_imps:
        if mod in BARRELS:
            continue
        is_test = rel.startswith(("LeanQbeTest/", "LeanQbeBootstrap0Test/"))
        is_leaf_test = is_test and rdep_counts.get(mod, 0) == 0
        for imp in imps:
            if imp.module in BARRELS:
                violations.append(
                    Violation(
                        leak_id="M6",
                        file=rel,
                        line=imp.line,
                        module=imp.module,
                        kind="m6-hub-import",
                        detail=(
                            f"forbidden hub/barrel import `{imp.module}` "
                            "(replace with minimal direct imports)"
                        ),
                    )
                )
            if is_leaf_test and imp.is_public:
                if imp.is_meta:
                    violations.append(
                        Violation(
                            leak_id="M6",
                            file=rel,
                            line=imp.line,
                            module=imp.module,
                            kind="m6-leaf-test-public-meta-import",
                            detail=(
                                f"leaf test (`rdeps == 0`) uses `public meta import "
                                f"{imp.module}` (use `meta import`)"
                            ),
                        )
                    )
                else:
                    violations.append(
                        Violation(
                            leak_id="M6",
                            file=rel,
                            line=imp.line,
                            module=imp.module,
                            kind="m6-leaf-test-public-import",
                            detail=(
                                f"leaf test (`rdeps == 0`) uses `public import "
                                f"{imp.module}` (use private `import`)"
                            ),
                        )
                    )
    return violations


def run_audit(
    root: Path,
    require_isa: bool = False,
    data_proof: bool = False,
    purity_ref: bool = False,
    purity_spec: bool = False,
    modsys: bool = False,
    modsys_report_only: bool = False,
    m5_allowlist: AbstractSet[str] | Mapping[str, AbstractSet[str]] | None = None,
) -> list[LeakGroupReport]:
    """Run firewall checks (`L1-L5`, optional `D1-D2`, `P-Ref`, `P-Spec`, `M1-M6`) against `root`."""
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
                    label="AST/Data -> Proof firewall (`Kissat/Src/*`)",
                    files=dp_files,
                    violations=d1_viols,
                ),
                LeakGroupReport(
                    leak_id="D2",
                    label=(
                        "Spurious printer/legal `meta import` firewall "
                        "(`Kissat/Src/*`)"
                    ),
                    files=dp_files,
                    violations=d2_viols,
                ),
            ]
        )
    if purity_ref:
        ref_files = discover_purity_ref_files(root)
        reports.append(
            LeakGroupReport(
                leak_id="P-Ref",
                label="Kissat `Ref/` purity (`0` proofs/tactics, `0` C0/Kraken/Spec/Proof imports)",
                files=ref_files,
                violations=check_purity_ref_files(root, ref_files, cache),
            )
        )
    if purity_spec:
        spec_files = discover_purity_spec_files(root)
        reports.append(
            LeakGroupReport(
                leak_id="P-Spec",
                label="Kissat `Spec/` purity (`0` proofs/deps/meta/cross-Spec/raw-idx/legacy)",
                files=spec_files,
                violations=check_purity_spec_files(root, spec_files, cache),
            )
        )
    if modsys or modsys_report_only:
        all_modsys_files = _discover_modsys_files(root)
        m1_files, m1_viols = check_m1_exec_meta_firewall(root, cache)
        m2_files, m2_viols = check_m2_build_cert_imports(root, all_modsys_files, cache)
        m3_viols = check_m3_public_meta_allowlist(root, all_modsys_files, cache)
        m4_files, m4_viols = check_m4_proof_public_imports(root, all_modsys_files, cache)
        m5_viols = check_m5_import_all_repo_wide(root, allowlist=m5_allowlist)
        m6_viols = check_m6_hub_and_leaf_tests(root, all_modsys_files, cache)
        m_ro = modsys_report_only
        reports.extend(
            [
                LeakGroupReport(
                    leak_id="M1",
                    label="Executable-root zero-proof `metaTransTrace` firewall",
                    files=m1_files,
                    violations=m1_viols,
                    report_only=m_ro,
                ),
                LeakGroupReport(
                    leak_id="M2",
                    label="`Build/*` & `*Cert*` elaborator/target import firewall",
                    files=m2_files,
                    violations=m2_viols,
                    report_only=m_ro,
                ),
                LeakGroupReport(
                    leak_id="M3",
                    label="`public meta import` allowlist",
                    files=all_modsys_files,
                    violations=m3_viols,
                    report_only=m_ro,
                ),
                LeakGroupReport(
                    leak_id="M4",
                    label="Proof-only `public import` ban (`Proof/` & `*Lemmas*`)",
                    files=m4_files,
                    violations=m4_viols,
                    report_only=m_ro,
                ),
                LeakGroupReport(
                    leak_id="M5",
                    label="Repo-wide zero `import all` (`LeanQbe*` & `LeanQbe*Test`)",
                    files=all_modsys_files,
                    violations=m5_viols,
                    report_only=m_ro,
                ),
                LeakGroupReport(
                    leak_id="M6",
                    label="Hub import ban & leaf-test hygiene (`rdeps == 0`)",
                    files=all_modsys_files,
                    violations=m6_viols,
                    report_only=m_ro,
                ),
            ]
        )
    return reports


def format_human_report(
    groups: list[LeakGroupReport],
    elapsed_ms: float,
    report_only: bool,
    *,
    max_per_group: int | None = None,
) -> str:
    """Render concise human-readable firewall report."""
    active_leaks = [g for g in groups if g.violations]
    total_viols = sum(len(g.violations) for g in groups)
    strict_viols = sum(
        len(g.violations) for g in groups if not (report_only or g.report_only)
    )
    mode = "report-only" if report_only else "strict"
    lines: list[str] = [
        f"firewall lint ({mode}, {elapsed_ms:.1f}ms): "
        f"{len(active_leaks)}/{len(groups)} leak group(s), "
        f"{total_viols} offending import(s) ({strict_viols} strict)"
    ]
    for g in groups:
        is_ro = report_only or g.report_only
        if g.violations:
            tag = "REPORT" if is_ro else "FAIL"
            status = f"{tag} ({len(g.violations)})"
        else:
            status = "OK"
        lines.append(f"[{g.leak_id}] {status}: {g.label}")
        if g.missing_files:
            lines.append(
                "  note: pre-P2B absent file(s): " + ", ".join(g.missing_files)
            )
        shown = g.violations if max_per_group is None else g.violations[:max_per_group]
        for v in shown:
            loc = f"{v.file}:{v.line}" if v.line > 0 else v.file
            lines.append(f"  - {loc}: {v.detail}")
        if max_per_group is not None and len(g.violations) > max_per_group:
            lines.append(f"  ... ({len(g.violations) - max_per_group} more)")
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
            "firewalls on `Kissat/Src/*` AST/Data modules."
        ),
    )
    ap.add_argument(
        "--purity-ref",
        action="store_true",
        help="Enforce Rule `P-Ref` purity on `**/Kissat*/Ref/*.lean` modules (opt-in).",
    )
    ap.add_argument(
        "--purity-spec",
        action="store_true",
        help="Enforce Rule `P-Spec` purity on `**/Kissat*/Spec/*.lean` and pre-W8 `Spec*` modules (opt-in).",
    )
    ap.add_argument(
        "--modsys",
        action="store_true",
        help="Enable Lean 4.37 module-system lints `M1`-`M6` (strict unless `--report-only`).",
    )
    ap.add_argument(
        "--modsys-report-only",
        action="store_true",
        help="Enable `M1`-`M6` in non-failing report-only mode (strict checks still fail).",
    )
    ap.add_argument(
        "--max-per-group",
        type=int,
        default=None,
        help="Optional cap on printed violations per group in human output.",
    )
    ap.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON output.",
    )
    args = ap.parse_args(argv)

    t0 = time.perf_counter()
    root = Path(args.root).resolve()
    groups = run_audit(
        root,
        require_isa=args.require_isa,
        data_proof=args.data_proof,
        purity_ref=args.purity_ref,
        purity_spec=args.purity_spec,
        modsys=args.modsys,
        modsys_report_only=args.modsys_report_only,
    )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0

    leak_groups = sum(1 for g in groups if g.violations)
    total_viols = sum(len(g.violations) for g in groups)
    strict_viols = sum(
        len(g.violations) for g in groups if not (args.report_only or g.report_only)
    )

    if args.json:
        payload = {
            "mode": "report-only" if args.report_only else "strict",
            "elapsed_ms": round(elapsed_ms, 2),
            "leak_groups": leak_groups,
            "total_violations": total_viols,
            "strict_violations": strict_viols,
            "groups": [
                {
                    "leak_id": g.leak_id,
                    "label": g.label,
                    "report_only": args.report_only or g.report_only,
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
        print(
            format_human_report(
                groups,
                elapsed_ms,
                args.report_only,
                max_per_group=args.max_per_group,
            )
        )

    if not args.report_only and strict_viols > 0:
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
