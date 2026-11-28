#!/usr/bin/env python3
"""Deterministic generator for subsystem-aligned declarative `Build/` certificates (`P1-6`).

Emits stable, position-free Lean modules mirroring a callee-first subsystem DAG (such as the
41 subsystems of `LeanQbe/T/Examples/Kissat/Src/Full.lean` or a custom JSON `--manifest`):

  1. `<Base>/Inl/<S>.lean`              - single `inline_seg!` call per subsystem
  2. `<Base>/Inl/Full.lean`             - O(#segs) `InlSeg.module_inlinePlan_fns_of_segs`
  3. `<Base>/{Amd64,Arm64}/<S>.lean`    - single `seg_cert!` call reading oracle `hints` & `ext`
  4. `<Base>/{Amd64,Arm64}/<S>/<fn>.lean` - single `fn_cert!` call per heavy fn (name-keyed)
  5. `<Base>/{Amd64,Arm64}/Full.lean`   - `LinkedCert.ofSegs` (or `ofCheckedSegGroups`) master

Repository invariants enforced on every emitted `.lean` file:
  - `module` header & `set_option autoImplicit false`
  - `<= 1500` LOC, `<= 100` cols, `0` `import all`, `0` `meta import ...Spill`
  - `0` positional `drop`/`take` slices below the master
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

MAX_LINE_LEN = 100
MAX_FILE_LINES = 1500
DEFAULT_HEAVY_THRESHOLD = 1000
DEFAULT_MAX_BOUND = 2048
DEFAULT_MAX_DIRS = 600


@dataclass(frozen=True)
class ArchInfo:
    """Architecture constants for declarative `seg_cert!` / `fn_cert!` / `Full.lean` emission."""

    key: str
    dir_name: str
    ns_prefix: str
    isa_title: str
    targ_mod: str
    lemmas_mod: str
    targ: str
    layout: str
    lt: str
    cl: str


ARCH_INFOS: dict[str, ArchInfo] = {
    "amd64": ArchInfo(
        key="amd64",
        dir_name="Amd64",
        ns_prefix="LeanQbe.T.Amd64",
        isa_title="SysV x64",
        targ_mod="LeanQbe.T.Amd64.Targ",
        lemmas_mod="LeanQbe.T.Amd64.TargLemmas",
        targ="x64Target",
        layout="x64Layout",
        lt="x64LegalTarget",
        cl="x64LabelClean",
    ),
    "arm64": ArchInfo(
        key="arm64",
        dir_name="Arm64",
        ns_prefix="LeanQbe.T.Arm64",
        isa_title="AAPCS64 Arm64",
        targ_mod="LeanQbe.T.Arm64.Targ",
        lemmas_mod="LeanQbe.T.Arm64.TargLemmas",
        targ="armTarget",
        layout="armLayout",
        lt="armLegalTarget",
        cl="armLabelClean",
    ),
}


@dataclass(frozen=True)
class SegSpec:
    """Metadata for one callee-first subsystem segment."""

    name: str
    src_mod: str
    src_fns: str
    fns: tuple[str, ...]
    deps: tuple[str, ...] = ()
    exports: tuple[str, ...] = ()
    heavy_fns: tuple[str, ...] = ()


@dataclass(frozen=True)
class BuildManifest:
    """Resolved subsystem DAG manifest for declarative `Build/` generation."""

    base_ns: str
    src_full_mod: str
    src_full_mod_sym: str
    segs: tuple[SegSpec, ...]
    max_bound: int = DEFAULT_MAX_BOUND
    max_dirs: int = DEFAULT_MAX_DIRS
    chunk_size: int = 1
    tree_groups: int = 0
    heavy_threshold: int = DEFAULT_HEAVY_THRESHOLD


SRC_FULL_APPEND_RE = re.compile(r"\b([A-Z][A-Za-z0-9_]*)\.fns\b")


def parse_src_full_subsystems(src_full_path: Path) -> list[str]:
    """Extract the ordered topological subsystem names from `Src/Full.lean`."""
    text = src_full_path.read_text(encoding="utf-8")
    m = re.search(r"def\s+kissatFns\s*:\s*List\s+Fn\s*:=(.*?)def\s+kissatModule", text, re.S)
    if not m:
        raise ValueError(f"could not locate `def kissatFns` block in {src_full_path}")
    names = SRC_FULL_APPEND_RE.findall(m.group(1))
    if not names:
        raise ValueError(f"no `<Subsystem>.fns` entries found in {src_full_path}")
    return names


def to_lean_ident(fn_name: str) -> str:
    """Convert a C/QBE symbol name into a valid PascalCase Lean module suffix."""
    parts = [p for p in re.split(r"[^A-Za-z0-9]+", fn_name) if p]
    if not parts:
        raise ValueError(f"cannot derive Lean module name from empty fn '{fn_name}'")
    out = "".join(p[0].upper() + p[1:] for p in parts)
    if not out[0].isalpha():
        out = "Fn" + out
    return out


def ns_to_rel_path(mod_ns: str) -> str:
    """Map a Lean module namespace (`A.B.C`) to its repo-relative path (`A/B/C.lean`)."""
    return "/".join(mod_ns.split(".")) + ".lean"


def wrap_line(prefix: str, items: list[str], indent: str = "  ", sep: str = " ") -> list[str]:
    """Wrap `prefix + sep.join(items)` cleanly within `MAX_LINE_LEN`."""
    if not items:
        return [prefix]
    one = f"{prefix}{sep.join(items)}"
    if len(one) <= MAX_LINE_LEN:
        return [one]
    lines: list[str] = []
    cur = prefix.rstrip()
    for idx, tok in enumerate(items):
        piece = tok if idx == 0 else tok
        joiner = " " if cur else ""
        if cur and len(cur) + len(joiner) + len(piece) <= MAX_LINE_LEN:
            cur = f"{cur}{joiner}{piece}"
        else:
            if cur:
                lines.append(cur)
            cur = f"{indent}{piece}"
    if cur:
        lines.append(cur)
    return lines


def load_profile_sizes(profile_path: Path) -> dict[str, int]:
    """Load per-function IR node counts or measured RAM metric from a JSON profile."""
    raw = json.loads(profile_path.read_text(encoding="utf-8"))
    out: dict[str, int] = {}
    if isinstance(raw, list):
        for row in raw:
            if isinstance(row, dict) and "name" in row:
                sz = int(
                    row.get(
                        "flat_size",
                        row.get("mid_tflat_size", row.get("ir_size", row.get("size", 0))),
                    )
                )
                out[str(row["name"])] = sz
    elif isinstance(raw, dict):
        for k, v in raw.items():
            if isinstance(v, (int, float)):
                out[str(k)] = int(v)
            elif isinstance(v, dict):
                out[str(k)] = int(
                    v.get("flat_size", v.get("mid_tflat_size", v.get("size", 0)))
                )
    else:
        raise ValueError(f"unsupported profile JSON format in {profile_path}")
    return out


def load_manifest(
    root: Path,
    manifest_path: Path | None,
    *,
    base_ns: str,
    src_full_mod: str,
    src_full_mod_sym: str,
    heavy_threshold: int,
    profile_path: Path | None,
    max_bound: int,
    max_dirs: int,
    chunk_size: int,
    tree_groups: int,
) -> BuildManifest:
    """Build a validated `BuildManifest` from `--manifest` JSON or `Src/Full.lean`."""
    if tree_groups < 0:
        raise ValueError(f"--tree-groups must be >= 0, got {tree_groups}")
    if chunk_size < 1:
        raise ValueError(f"--chunk-size must be >= 1, got {chunk_size}")
    prof = load_profile_sizes(profile_path) if profile_path else {}

    if manifest_path is not None:
        raw = json.loads(manifest_path.read_text(encoding="utf-8"))
        m_base_ns = str(raw.get("base_ns", base_ns))
        m_src_full = str(raw.get("src_full_mod", src_full_mod))
        m_src_sym = str(raw.get("src_full_mod_sym", src_full_mod_sym))
        raw_segs = raw.get("segs", [])
        if not isinstance(raw_segs, list) or not raw_segs:
            raise ValueError(f"manifest {manifest_path} must contain a non-empty `segs` list")
        seen_names: list[str] = []
        segs: list[SegSpec] = []
        for entry in raw_segs:
            nm = str(entry["name"])
            if nm in seen_names:
                raise ValueError(f"duplicate segment '{nm}' in manifest")
            deps = tuple(str(d) for d in entry.get("deps", []))
            for d in deps:
                if d not in seen_names:
                    raise ValueError(
                        f"segment '{nm}' depends on '{d}' which does not precede it (DAG violation)"
                    )
            fns = tuple(str(f) for f in entry.get("fns", []))
            exports = tuple(str(e) for e in entry.get("exports", []))
            for e in exports:
                if fns and e not in fns:
                    raise ValueError(f"segment '{nm}' exports unknown fn '{e}'")
            explicit_heavy = [str(h) for h in entry.get("heavy_fns", [])]
            prof_heavy = [
                f for f in fns if f not in explicit_heavy and prof.get(f, 0) >= heavy_threshold
            ]
            heavy = tuple(explicit_heavy + prof_heavy)
            segs.append(
                SegSpec(
                    name=nm,
                    src_mod=str(entry["src_mod"]),
                    src_fns=str(entry.get("src_fns", "fns")),
                    fns=fns,
                    deps=deps,
                    exports=exports,
                    heavy_fns=heavy,
                )
            )
            seen_names.append(nm)
        return BuildManifest(
            base_ns=m_base_ns,
            src_full_mod=m_src_full,
            src_full_mod_sym=m_src_sym,
            segs=tuple(segs),
            max_bound=max_bound,
            max_dirs=max_dirs,
            chunk_size=chunk_size,
            tree_groups=tree_groups,
            heavy_threshold=heavy_threshold,
        )

    src_full_file = root / ns_to_rel_path(src_full_mod)
    sub_names = parse_src_full_subsystems(src_full_file)
    src_pkg = src_full_mod.rsplit(".", 1)[0]
    segs = [
        SegSpec(
            name=nm,
            src_mod=f"{src_pkg}.{nm}",
            src_fns="fns",
            fns=(),
            deps=(),
            exports=(),
            heavy_fns=(),
        )
        for nm in sub_names
    ]
    return BuildManifest(
        base_ns=base_ns,
        src_full_mod=src_full_mod,
        src_full_mod_sym=src_full_mod_sym,
        segs=tuple(segs),
        max_bound=max_bound,
        max_dirs=max_dirs,
        chunk_size=chunk_size,
        tree_groups=tree_groups,
        heavy_threshold=heavy_threshold,
    )


def _format_kv_list(key: str, elems: list[str], sep: str, open_ch: str, close_ch: str) -> list[str]:
    """Format `(<key> := <open><elems joined by sep><close>)` wrapped within `MAX_LINE_LEN`."""
    one = f"({key} := {open_ch}{sep.join(elems)}{close_ch})"
    if len(one) + 2 <= MAX_LINE_LEN:
        return [f"  {one}"]
    out = [f"  ({key} := {open_ch}".rstrip()]
    for idx, el in enumerate(elems):
        if sep == ", ":
            tail = "," if idx + 1 < len(elems) else f"{close_ch})"
            out.append(f"    {el}{tail}")
        else:
            pfx = "    " if idx == 0 else f"    {sep.strip()} "
            tail = f"{close_ch})" if idx + 1 == len(elems) else ""
            out.append(f"{pfx}{el}{tail}")
    return out


def render_inl_seg(mf: BuildManifest, seg: SegSpec) -> str:
    """Render declarative `<Base>/Inl/<S>.lean` calling `inline_seg!`."""
    ns = f"{mf.base_ns}.Inl.{seg.name}"
    oracle_mod = f"{mf.base_ns}.Oracle.{seg.name}"
    exp_mod = f"{mf.base_ns}.Inl.{seg.name}.Exports"

    pub_imports = [
        "public import LeanQbe.T.InlinePlanSeg",
        f"public import {seg.src_mod}",
        f"public import {oracle_mod}",
    ]
    for dep in seg.deps:
        pub_imports.append(f"public import {mf.base_ns}.Inl.{dep}.Exports")
    if seg.exports:
        pub_imports.append(f"public import {exp_mod}")

    meta_imports = [
        "meta import Lean",
        "meta import LeanQbe.T.MainCertSegElab",
        f"meta import {seg.src_mod}",
        f"meta import {oracle_mod}",
    ]
    for dep in seg.deps:
        meta_imports.append(f"meta import {mf.base_ns}.Inl.{dep}.Exports")

    cmd_lines = wrap_line(
        "inline_seg! inl ",
        [f"{seg.src_mod}.{seg.src_fns}", f"(plan := {oracle_mod}.plan)"],
        indent="  ",
    )
    if seg.deps:
        dep_elems = [f"{mf.base_ns}.Inl.{d}.Exports.fns" for d in seg.deps]
        cmd_lines.extend(_format_kv_list("deps", dep_elems, " ++ ", "", ""))
    if seg.exports:
        cmd_lines.append(f"  (exports := {exp_mod}.fns)")

    lines = [
        "module",
        "",
        *pub_imports,
        *meta_imports,
        "",
        "/-!",
        f"# Plan-Inlined Subsystem `{seg.name}`",
        "",
        "Declarative subsystem inlining leaf (`inline_seg!`). Imports only `Src` + local `Oracle`",
        "+ dependency `Exports` leaves.",
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        "open LeanQbe.T",
        "open scoped LeanQbe.T",
        "",
        *cmd_lines,
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def _render_dep_sub_lines(
    mf: BuildManifest,
    prev_segs: list[SegSpec],
    dep_name: str,
    indent: str,
) -> list[str]:
    """Build wrapped `forall_mem_mono_append_*` proof lines for `dep_name.Exports.fns`."""
    idx = next(i for i, s in enumerate(prev_segs) if s.name == dep_name)
    base = f"{mf.base_ns}.Inl.{dep_name}.inl.exports_sub"
    lefts = len(prev_segs) - (idx + 1)
    tokens = ["InlSeg.forall_mem_mono_append_left <|" for _ in range(lefts)]
    tokens.append(f"InlSeg.forall_mem_mono_append_right {base}")
    return wrap_line(indent, tokens, indent=indent)


def _render_deps_mem_lines(
    mf: BuildManifest,
    prev_segs: list[SegSpec],
    deps: tuple[str, ...],
    indent: str,
) -> list[str]:
    """Build wrapped proof lines for `∀ e ∈ seg.depsExports, e ∈ prevFns`."""
    if not deps:
        return [f"{indent}InlSeg.forall_mem_nil,"]
    if len(deps) == 1:
        res = _render_dep_sub_lines(mf, prev_segs, deps[0], indent)
        res[-1] = res[-1] + ","
        return res

    def emit_chain(k: int, ind: str) -> list[str]:
        if k == 0:
            return _render_dep_sub_lines(mf, prev_segs, deps[0], ind)
        lhs = emit_chain(k - 1, ind + "  ")
        rhs = _render_dep_sub_lines(mf, prev_segs, deps[k], ind + "  ")
        lhs[0] = f"{ind}  (" + lhs[0].lstrip()
        lhs[-1] = lhs[-1] + ")"
        rhs[0] = f"{ind}  (" + rhs[0].lstrip()
        rhs[-1] = rhs[-1] + ")"
        return [f"{ind}InlSeg.forall_mem_append_elim", *lhs, *rhs]

    out = emit_chain(len(deps) - 1, indent)
    out[-1] = out[-1] + ","
    return out


def render_inl_full(mf: BuildManifest) -> str:
    """Render `<Base>/Inl/Full.lean` joining all subsystem `InlSeg`s in `O(#segs)`."""
    ns = f"{mf.base_ns}.Inl.Full"
    pub_imports = [
        "public import LeanQbe.T.InlinePlanSeg",
        f"public import {mf.src_full_mod}",
    ]
    for seg in mf.segs:
        pub_imports.append(f"public import {mf.base_ns}.Oracle.{seg.name}")
        pub_imports.append(f"public import {mf.base_ns}.Inl.{seg.name}")

    plan_terms = [f"{mf.base_ns}.Oracle.{s.name}.plan" for s in mf.segs]
    seg_terms = [f"{mf.base_ns}.Inl.{s.name}.inl.seg" for s in mf.segs]
    src_mod_ref = f"{mf.src_full_mod}.{mf.src_full_mod_sym}"

    lines = [
        "module",
        "",
        *pub_imports,
        "",
        "/-!",
        f"# Whole-Module Plan-Inlined Assembly (`{len(mf.segs)}` Subsystems)",
        "",
        "Assembles `(srcMod.inlinePlan fullPlan).fns = InlSeg.allFns allSegs` in `O(#segs)`",
        "without unfolding any function bodies.",
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        "open LeanQbe.T",
        "",
        "/-- Concatenated whole-module inline plan across all subsystems. -/",
        "@[expose] def fullPlan : InlPlan :=",
    ]
    for idx, pt in enumerate(plan_terms):
        pfx = "  " if idx == 0 else "  ++ "
        lines.append(f"{pfx}{pt}")
    lines.extend(
        [
            "",
            "/-- Ordered list of per-subsystem materialized `InlSeg` certificates. -/",
            "@[expose] noncomputable def allSegs : List InlSeg := [",
        ]
    )
    for idx, st in enumerate(seg_terms):
        comma = "," if idx + 1 < len(seg_terms) else ""
        lines.append(f"  {st}{comma}")
    lines.extend(
        [
            "]",
            "",
            "/-- Concatenated post-inline function list across all subsystems. -/",
            "@[expose] noncomputable def inlFns : List Fn := InlSeg.allFns allSegs",
            "",
            "private theorem allSrc_eq :",
            f"    {src_mod_ref}.fns =",
            "      InlSeg.allSrcFns allSegs := rfl",
            "",
            "private theorem allNames_nodup :",
            "    listNodup ((InlSeg.allSrcFns allSegs).map Fn.name) = true := by",
            "  decide",
            "",
            "private theorem deps_ok : InlSeg.DepsOkFrom fullPlan [] [] allSegs := by",
            "  refine",
        ]
    )
    prev_segs: list[SegSpec] = []
    for seg in mf.segs:
        indent = "    "
        lines.append(f"{indent}⟨by decide,")
        lines.extend(_render_deps_mem_lines(mf, prev_segs, seg.deps, f"{indent} "))
        lines.append(f"{indent} by decide,")
        prev_segs.append(seg)
    lines.append("    trivial" + "⟩" * len(mf.segs))
    lines.extend(
        [
            "",
            "/-- Whole-module plan-inlining equality proved in `O(#segs)` via `InlinePlanSeg`. -/",
            "theorem inlFns_eq :",
            f"    ({src_mod_ref}.inlinePlan fullPlan).fns =",
            "      inlFns :=",
            "  InlSeg.module_inlinePlan_fns_of_segs",
            f"    {src_mod_ref} fullPlan allSegs",
            "    allSrc_eq allNames_nodup deps_ok",
            "",
            f"end {ns}",
            "",
        ]
    )
    return "\n".join(lines)


def _split_non_heavy_runs(
    fns: tuple[str, ...], heavy_fns: tuple[str, ...]
) -> list[tuple[str, int, int | str]]:
    """Return ordered sequence of `('part', part_idx, count)` and `('heavy', fn_idx, fn_name)`."""
    if not heavy_fns:
        return [("seg", 0, len(fns))]
    heavy_set = set(heavy_fns)
    out: list[tuple[str, int, int | str]] = []
    part_idx = 0
    in_run = 0
    for idx, fn in enumerate(fns):
        if fn in heavy_set:
            if in_run > 0:
                out.append(("part", part_idx, in_run))
                part_idx += 1
                in_run = 0
            out.append(("heavy", idx, fn))
        else:
            in_run += 1
    if in_run > 0:
        out.append(("part", part_idx, in_run))
    return out


def render_arch_seg(mf: BuildManifest, arch: ArchInfo, seg: SegSpec) -> str:
    """Render declarative `<Base>/{Amd64,Arm64}/<S>.lean` calling `seg_cert!`."""
    ns = f"{mf.base_ns}.{arch.dir_name}.{seg.name}"
    inl_mod = f"{mf.base_ns}.Inl.{seg.name}"
    oracle_mod = f"{mf.base_ns}.Oracle.{arch.dir_name}.{seg.name}"

    items = [
        f"{inl_mod}.inl.fns",
        f"(hints := {oracle_mod}.hints)",
        f"(ext := {oracle_mod}.ext)",
        f"(chunkSize := {mf.chunk_size})",
        f"(maxDirs := {mf.max_dirs})",
        f"(maxBound := {mf.max_bound})",
        "(pruneExt := true)",
    ]
    cmd_head = f"seg_cert! cert {arch.targ} {arch.layout} {arch.lt} {arch.cl} "
    cmd_lines = wrap_line(cmd_head, items, indent="  ")
    if seg.heavy_fns:
        excl_elems = [f'"{h}"' for h in seg.heavy_fns]
        cmd_lines.extend(_format_kv_list("exclude", excl_elems, ", ", "[", "]"))

    lines = [
        "module",
        "",
        "public import LeanQbe.T.MainCertSeg",
        "public import LeanQbe.T.MainCertFlat",
        f"public import {arch.lemmas_mod}",
        f"public import {inl_mod}",
        "meta import Lean",
        "meta import LeanQbe.T.MainCertSegElab",
        f"meta import {arch.targ_mod}",
        f"meta import {oracle_mod}",
        "",
        "/-!",
        f"# Declarative Subsystem Cert `{seg.name}` on {arch.isa_title}",
        "",
        "Zero `Spill` meta import; reads precomputed oracle `hints` and `ext`.",
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        f"open LeanQbe.T {arch.ns_prefix}",
        "open scoped LeanQbe.T",
        "",
        *cmd_lines,
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_arch_heavy_fn(
    mf: BuildManifest, arch: ArchInfo, seg: SegSpec, fn_idx: int, fn_name: str
) -> str:
    """Render name-keyed `<Base>/{Amd64,Arm64}/<S>/<Fn>.lean` calling `fn_cert!`."""
    fn_mod_id = to_lean_ident(fn_name)
    ns = f"{mf.base_ns}.{arch.dir_name}.{seg.name}.{fn_mod_id}"
    inl_mod = f"{mf.base_ns}.Inl.{seg.name}"
    oracle_mod = f"{mf.base_ns}.Oracle.{arch.dir_name}.{seg.name}"

    items = [
        f"{inl_mod}.inl.flat.f{fn_idx}",
        f"(hints := {oracle_mod}.hint_{fn_name})",
        f"(ext := {oracle_mod}.ext_{fn_name})",
        f"(maxBound := {mf.max_bound})",
        "(pruneExt := true)",
    ]
    cmd_head = f"fn_cert! cert {arch.targ} {arch.layout} {arch.lt} {arch.cl} "
    cmd_lines = wrap_line(cmd_head, items, indent="  ")

    lines = [
        "module",
        "",
        "public import LeanQbe.T.MainCertSeg",
        "public import LeanQbe.T.MainCertFlat",
        f"public import {arch.lemmas_mod}",
        f"public import {inl_mod}",
        "meta import Lean",
        "meta import LeanQbe.T.MainCertSegElab",
        f"meta import {arch.targ_mod}",
        f"meta import {oracle_mod}",
        "",
        "/-!",
        f"# Isolated Heavy Function Cert `{seg.name}.{fn_name}` on {arch.isa_title}",
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        f"open LeanQbe.T {arch.ns_prefix}",
        "open scoped LeanQbe.T",
        "",
        *cmd_lines,
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_arch_full(mf: BuildManifest, arch: ArchInfo) -> str:
    """Render `<Base>/{Amd64,Arm64}/Full.lean` assembling `LinkedCert.ofSegs`."""
    ns = f"{mf.base_ns}.{arch.dir_name}.Full"
    inl_full = f"{mf.base_ns}.Inl.Full"

    pub_imports = [
        "public import LeanQbe.T.MainCertSeg",
        f"public import {arch.lemmas_mod}",
        f"public import {mf.src_full_mod}",
        f"public import {inl_full}",
    ]
    seg_exprs: list[str] = []
    for seg in mf.segs:
        seg_mod = f"{mf.base_ns}.{arch.dir_name}.{seg.name}"
        pub_imports.append(f"public import {seg_mod}")
        runs = _split_non_heavy_runs(seg.fns, seg.heavy_fns)
        for kind, idx, info in runs:
            if kind == "seg":
                seg_exprs.append(f"{seg_mod}.cert")
            elif kind == "part":
                seg_exprs.append(f"{seg_mod}.cert.part{idx}")
            else:
                fn_id = to_lean_ident(str(info))
                hmod = f"{seg_mod}.{fn_id}"
                pub_imports.append(f"public import {hmod}")
                seg_exprs.append(f"{hmod}.cert")

    src_mod_ref = f"{mf.src_full_mod}.{mf.src_full_mod_sym}"

    lines = [
        "module",
        "",
        *pub_imports,
        "",
        "/-!",
        f"# Whole-Module Subsystem-Aligned Certificate on {arch.isa_title}",
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        f"open LeanQbe.T {arch.ns_prefix}",
        "",
        "/-- Plan-inlined whole module certified by `fullCert`. -/",
        "@[expose] def inlMod : Module :=",
        f"  {src_mod_ref}.inlinePlan",
        f"    {inl_full}.fullPlan",
        "",
        "/-- Ordered list of subsystem and isolated heavy-function `SegChunks`. -/",
        "@[expose] noncomputable def allSegChunks :",
        f"    List (SegChunks {arch.targ} {arch.lt} [] 0 {mf.max_bound}) := [",
    ]
    for idx, se in enumerate(seg_exprs):
        comma = "," if idx + 1 < len(seg_exprs) else ""
        lines.append(f"  {se}{comma}")
    lines.extend(
        [
            "]",
            "",
            "/-- Function-list alignment between `inlMod` and `allSegChunks`. -/",
            "theorem allSegs_fns_eq :",
            "    inlMod.fns = SegChunks.allFns allSegChunks := by",
            "  unfold inlMod",
            f"  rw [{inl_full}.inlFns_eq]",
            "  rfl",
            "",
            "/-- Whole-module cross-segment link check across `allSegChunks`. -/",
            "theorem allSegs_link :",
            f"    checkLinkList {arch.layout} [] (SegChunks.allChunks allSegChunks) = true := by",
            "  rfl",
            "",
            "/-- Whole-module verified `LinkedCert` assembled via `LinkedCert.ofSegs`. -/",
            "@[expose] noncomputable def fullCert :",
            f"    LinkedCert {arch.targ} {arch.layout} {arch.lt} {arch.cl}",
            f"      inlMod [] [] 0 {mf.max_bound} :=",
            "  LinkedCert.ofSegs allSegChunks allSegs_fns_eq allSegs_link",
            "",
            f"end {ns}",
            "",
        ]
    )
    return "\n".join(lines)


def validate_files(files: list[tuple[str, str]]) -> None:
    """Enforce P0-5 hygiene and zero-Spill invariants on every generated file."""
    for rel, content in files:
        lines = content.splitlines()
        if not lines or lines[0] != "module":
            raise ValueError(f"{rel}: missing `module` header")
        if "set_option autoImplicit false" not in content:
            raise ValueError(f"{rel}: missing `set_option autoImplicit false`")
        if len(lines) > MAX_FILE_LINES:
            raise ValueError(f"{rel}: {len(lines)} lines > {MAX_FILE_LINES}")
        if "import all " in content:
            raise ValueError(f"{rel}: forbidden `import all`")
        if re.search(r"meta\s+import\s+LeanQbe\.T\.Spill\b", content):
            raise ValueError(f"{rel}: forbidden `meta import LeanQbe.T.Spill`")
        for idx, ln in enumerate(lines, start=1):
            if len(ln) > MAX_LINE_LEN:
                raise ValueError(f"{rel}:{idx}: {len(ln)} cols > {MAX_LINE_LEN}: {ln}")


def build_plan(mf: BuildManifest, arches: list[str]) -> list[tuple[str, str]]:
    """Build deterministic `(rel_path, lean_source)` pairs for the declarative `Build/` tree."""
    files: list[tuple[str, str]] = []
    for seg in mf.segs:
        files.append((ns_to_rel_path(f"{mf.base_ns}.Inl.{seg.name}"), render_inl_seg(mf, seg)))
    files.append((ns_to_rel_path(f"{mf.base_ns}.Inl.Full"), render_inl_full(mf)))
    for arch_key in arches:
        arch = ARCH_INFOS[arch_key]
        for seg in mf.segs:
            files.append(
                (
                    ns_to_rel_path(f"{mf.base_ns}.{arch.dir_name}.{seg.name}"),
                    render_arch_seg(mf, arch, seg),
                )
            )
            for fn_name in seg.heavy_fns:
                fn_idx = seg.fns.index(fn_name)
                fn_id = to_lean_ident(fn_name)
                files.append(
                    (
                        ns_to_rel_path(f"{mf.base_ns}.{arch.dir_name}.{seg.name}.{fn_id}"),
                        render_arch_heavy_fn(mf, arch, seg, fn_idx, fn_name),
                    )
                )
        files.append(
            (ns_to_rel_path(f"{mf.base_ns}.{arch.dir_name}.Full"), render_arch_full(mf, arch))
        )
    validate_files(files)
    return files


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    ap = argparse.ArgumentParser(
        description="Deterministic generator for subsystem-aligned declarative Build/ certs."
    )
    ap.add_argument("--root", default=".", help="Repository root (default: .).")
    ap.add_argument("--out-dir", default=".", help="Output root directory (default: .).")
    ap.add_argument(
        "--manifest",
        help="Optional JSON subsystem DAG manifest (default: parse Src/Full.lean).",
    )
    ap.add_argument(
        "--base-ns",
        default="LeanQbe.T.Examples.Kissat.Build",
        help="Target Lean namespace root for generated Build/ modules.",
    )
    ap.add_argument(
        "--src-full-mod",
        default="LeanQbe.T.Examples.Kissat.Src.Full",
        help="Source full module containing concatenated subsystem fns.",
    )
    ap.add_argument(
        "--src-full-mod-sym",
        default="kissatModule",
        help="Module identifier in --src-full-mod (default: kissatModule).",
    )
    ap.add_argument(
        "--arch",
        choices=("both", "amd64", "arm64"),
        default="both",
        help="Target architectures (default: both).",
    )
    ap.add_argument(
        "--profile",
        help="Optional per-fn size/RAM JSON profile for automatic heavy-fn isolation.",
    )
    ap.add_argument(
        "--heavy-threshold",
        type=int,
        default=DEFAULT_HEAVY_THRESHOLD,
        help=(
            "IR node-count floor for name-keyed fn_cert! isolation "
            f"(default: {DEFAULT_HEAVY_THRESHOLD})."
        ),
    )
    ap.add_argument("--max-bound", type=int, default=DEFAULT_MAX_BOUND)
    ap.add_argument("--max-dirs", type=int, default=DEFAULT_MAX_DIRS)
    ap.add_argument("--chunk-size", type=int, default=1)
    ap.add_argument("--tree-groups", type=int, default=0)
    ap.add_argument("--dry-run", action="store_true", help="Validate without writing files.")
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint."""
    args = parse_args(argv)
    try:
        mf = load_manifest(
            Path(args.root).resolve(),
            Path(args.manifest) if args.manifest else None,
            base_ns=args.base_ns,
            src_full_mod=args.src_full_mod,
            src_full_mod_sym=args.src_full_mod_sym,
            heavy_threshold=args.heavy_threshold,
            profile_path=Path(args.profile) if args.profile else None,
            max_bound=args.max_bound,
            max_dirs=args.max_dirs,
            chunk_size=args.chunk_size,
            tree_groups=args.tree_groups,
        )
        arches = ["amd64", "arm64"] if args.arch == "both" else [args.arch]
        files = build_plan(mf, arches)
    except ValueError as err:
        print(f"error: {err}", file=sys.stderr)
        return 1

    mode = "dry-run" if args.dry_run else "write"
    heavy_cnt = sum(len(s.heavy_fns) for s in mf.segs)
    print(
        f"gen_build_segs ({mode}): segs={len(mf.segs)} heavy={heavy_cnt} "
        f"arch={args.arch} files={len(files)}"
    )
    if args.dry_run:
        for rel, content in files:
            print(f"  [plan] {rel} ({len(content.splitlines())}L)")
        return 0
    out_root = Path(args.out_dir).resolve()
    for rel, content in files:
        dest = out_root / rel
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(content, encoding="utf-8")
        print(f"  [wrote] {dest}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
