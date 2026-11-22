#!/usr/bin/env python3
"""Deterministic CLI generator for cost-balanced 1-tier Kissat solver cert slices.

Generates five Lean module families per architecture (`Amd64`, `Arm64`):
  1. `<Prefix>Bounds.lean`     - `eval_prefix_ext!` + `<stem>ExtPrefix`
  2. `<Prefix>Cert1..N.lean`   - `<= 12` fns/slice (`compile_linked_chunks!`)
  3. `<Prefix>Cert.lean`       - flat `LinkedCert.append` ladder
  4. `<Prefix>CertLink.lean`   - `<stem>_legalSig`, `mk_module_fnspec`,
                                 `solve_{x64,arm64}_of_fnspec`
  5. `<Prefix>.lean`           - compiled cert alias, `*_module_fnspec`,
                                 and UNSAT correctness wrappers

Supports:
  - `--module FullM5` (matching `M5Hub` and `MainCertCore`/`Proof`/`Elab`
    noncomputable cert-def pattern from `feed185f`) alongside `FullM4`, `FullM3`,
    `FullFast`, `FullFastSched`, `Full`, and `Plain`.
  - LPT (Longest-Processing-Time-first) cost-weighted bin-packing and
    straggler-isolated contiguous slicing driven either by a Lean `--profile`
    JSON table or by built-in static C0/AST complexity estimation (`r ~ 0.98`).
  - Repository invariants on every emitted `.lean` file: `module`,
    `set_option autoImplicit false`, `<= 3000` LOC, `<= 100c` line width, `0`
    `import all`, and single-line `< 115c` `#print axioms`.
"""

from __future__ import annotations

import argparse
import json
import math
import re
import sys
from dataclasses import dataclass
from pathlib import Path

MAX_LINE_LEN = 100
MAX_FILE_LINES = 3000
MAX_SLICE_SIZE = 12
MAX_AXIOM_REPORT_LEN = 114  # Strictly < 115c (`scripts/check.sh` rule).
DEFAULT_WORKERS = 16
DEFAULT_FILE_OVERHEAD = 100.0
DEFAULT_M5_TOTAL_FNS = 234

# Worst-case axiom report text suffix length:
#   '<ns>.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
# quotes (2) + dot (1) + " depends on axioms: [propext, Classical.choice, Quot.sound]" (59)
AXIOM_REPORT_FIXED_OVERHEAD = 62

# Known kernel-elaboration stragglers in Kissat C0 modules (including `_m5` suffix).
SINGLETON_STRAGGLER_RE = re.compile(
    r"^full_(?:prop_lit_raw|cong_work_step|k512_.*|bcp_.*|bva_scan_cands)(?:_m\d+)?$"
)
HEAVY_FAMILY_RE = re.compile(
    r"^full_(?:bva_.*|viv_.*|sweep_var.*|fwd_check_cl.*|find_definition.*|"
    r"bve_var.*|factor.*|trans_lit.*|probe_prop_lit.*|substitute.*|analyze.*|"
    r"kitten_solve.*|kitten_core.*)(?:_m\d+)?$"
)

C_TYPE_RE = (
    r"(?:static\s+|inline\s+)*(?:const\s+)?"
    r"(?:u8|u16|u32|u64|i8|i16|i32|i64|s32|s64|"
    r"uint64_t|uint32_t|int64_t|int32_t|int|void|bool|size_t)\s*\*?\s*"
)
C_FN_HDR_RE = re.compile(C_TYPE_RE + r"([a-zA-Z_][a-zA-Z0-9_]*)\s*\([^;{}]*?\)\s*\{")
C0_BLOCK_RE = re.compile(r'kissat_c0!\s+(\S+)\s+"(.*?)"(?=\s*\n)', re.S)


@dataclass(frozen=True)
class ArchSpec:
    """Architecture-specific Lean identifiers and proof templates."""

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
    arch_tag: str
    kraken_isa: str
    of_returns_fn: str
    of_returns_args: str
    ret_reg: str
    callee_saved_pred: tuple[str, ...]
    sp_ret: str
    solve_link_hyps: tuple[str, ...]
    solve_stack_post: tuple[str, ...]
    solve_hargs_chain: tuple[str, ...]
    solve_rintro_cal: str
    rets_extract_lines: tuple[str, ...]
    solve_call_hyps: str
    unsat_solve_call_hyps: str
    unsat_rintro_cal: str
    unsat_rintro_sp: str

    def unsat_reg_hyps(self, bound_expr: str) -> list[str]:
        if self.key == "amd64":
            return [
                "  (hrdi : s.regs.get64 .rdi = cnf_ptr)",
                "  (hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)",
                "  (hrdx : s.regs.get64 .rdx = work_ptr)",
                "  (hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)",
                "  (hr8 : s.regs.get64 .r8 = fuel)",
                "  (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)",
                "  (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
                "    (region (s.regs.get64 .rsp - BitVec.ofNat 64",
                f"        {bound_expr})",
                f"      {bound_expr} ⋆",
                "      cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem)",
            ]
        return [
            "  (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)",
            "  (hx1 : (s.regs.getXReg .X1).toBitVec = "
            "BitVec.ofNat 64 cnfBytes.length)",
            "  (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)",
            "  (hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)",
            "  (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)",
            "  (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)",
            "  (hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
            "    region (s.regs.SP.toBitVec - BitVec.ofNat 64",
            f"        {bound_expr})",
            f"      {bound_expr} ⋆ R) s.dmem)",
        ]

    def unsat_st_dmem(self, bound_expr: str) -> list[str]:
        if self.key == "amd64":
            return [
                "        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
                "          region (s.regs.get64 .rsp - BitVec.ofNat 64",
                f"              {bound_expr})",
                f"            ({bound_expr} + 8) ⋆ R)",
                "          st.data.dmem)",
            ]
        return [
            "        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
            "          region (s.regs.SP.toBitVec - BitVec.ofNat 64",
            f"              {bound_expr})",
            f"            {bound_expr} ⋆ R)",
            "          st.data.dmem)",
        ]

    def unsat_hm0(self, bound_expr: str) -> list[str]:
        if self.key == "amd64":
            return [
                "  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆",
                "      ((region (s.regs.get64 .rsp - BitVec.ofNat 64",
                f"          {bound_expr})",
                f"        {bound_expr} ⋆",
                "        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R)) s.dmem := by",
            ]
        return [
            "  have hm0 : ((bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) ⋆",
            "      (region (s.regs.SP.toBitVec - BitVec.ofNat 64",
            f"          {bound_expr})",
            f"        {bound_expr} ⋆ R)) s.dmem := by",
        ]

    def unsat_hm_dmem(self, bound_expr: str) -> list[str]:
        if self.key == "amd64":
            return [
                "  have hm_dmem' : (Eq m ⋆",
                "      (region (s.regs.get64 .rsp - BitVec.ofNat 64",
                f"          {bound_expr})",
                f"        {bound_expr} ⋆",
                "        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem := by",
            ]
        return [
            "  have hm_dmem' : (Eq m ⋆",
            "      region (s.regs.SP.toBitVec - BitVec.ofNat 64",
            f"          {bound_expr})",
            f"        {bound_expr} ⋆ R) s.dmem := by",
        ]


ARCH_SPECS: dict[str, ArchSpec] = {
    "amd64": ArchSpec(
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
        arch_tag="x64",
        kraken_isa="Kraken-x64",
        of_returns_fn="x64_of_returns",
        of_returns_args="hsp hmem",
        ret_reg="st.data.regs.get64 .rax",
        callee_saved_pred=(
            "        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],",
            "          st.data.regs.get64 r = s.regs.get64 r) ∧",
        ),
        sp_ret="st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64",
        solve_link_hyps=(
            "    (hrdi : s.regs.get64 .rdi = cnf_ptr)",
            "    (hrsi : s.regs.get64 .rsi = cnf_len)",
            "    (hrdx : s.regs.get64 .rdx = work_ptr)",
            "    (hrcx : s.regs.get64 .rcx = work_len)",
            "    (hr8 : s.regs.get64 .r8 = fuel)",
            "    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)",
            "    (hmem : s.dmem =⋆ Eq m ⋆",
            "      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆",
            "        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :",
        ),
        solve_stack_post=(
            "            region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))",
        ),
        solve_hargs_chain=(
            "      .cons ⟨by decide, by simpa using hrdi⟩",
            "        (.cons ⟨by decide, by simpa using hrsi⟩",
            "          (.cons ⟨by decide, by simpa using hrdx⟩",
            "            (.cons ⟨by decide, by simpa using hrcx⟩",
            "              (.cons ⟨by decide, by simpa using hr8⟩ .nil))))⟩",
        ),
        solve_rintro_cal="hcs",
        rets_extract_lines=(
            "  have hrax : st.data.regs.get64 .rax = r :=",
            "    x64Init.retsIn_singleton r st.data hrets",
            "  rw [hrax]",
        ),
        solve_call_hyps="hrdi hrsi hrdx hrcx hr8 hsp hmem",
        unsat_solve_call_hyps="hrdi hrsi hrdx hrcx hr8 hsp hm_dmem'",
        unsat_rintro_cal="hcal",
        unsat_rintro_sp="hrsp",
    ),
    "arm64": ArchSpec(
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
        arch_tag="arm64",
        kraken_isa="Kraken-AArch64",
        of_returns_fn="arm64_of_returns",
        of_returns_args="hra hsp hmem",
        ret_reg="(st.data.regs.getXReg .X0).toBitVec",
        callee_saved_pred=(
            "        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,",
            "            .X27, .X28, .X29],",
            "          st.data.regs.getXReg r = s.regs.getXReg r) ∧",
        ),
        sp_ret="st.data.regs.SP = s.regs.SP",
        solve_link_hyps=(
            "    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)",
            "    (hx1 : (s.regs.getXReg .X1).toBitVec = cnf_len)",
            "    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)",
            "    (hx3 : (s.regs.getXReg .X3).toBitVec = work_len)",
            "    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)",
            "    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)",
            "    (hmem : s.dmem =⋆ Eq m ⋆",
            "      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :",
        ),
        solve_stack_post=(
            "            region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))",
        ),
        solve_hargs_chain=(
            "      .cons ⟨by decide, by simpa [get_reg] using hx0⟩",
            "        (.cons ⟨by decide, by simpa [get_reg] using hx1⟩",
            "          (.cons ⟨by decide, by simpa [get_reg] using hx2⟩",
            "            (.cons ⟨by decide, by simpa [get_reg] using hx3⟩",
            "              (.cons ⟨by decide, by simpa [get_reg] using hx4⟩ .nil))))⟩",
        ),
        solve_rintro_cal="hcal",
        rets_extract_lines=(
            "  have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by",
            "    simpa [armInit, get_reg] using armInit.retsIn_singleton r st.data hrets",
            "  rw [hx0']",
        ),
        solve_call_hyps="hx0 hx1 hx2 hx3 hx4 hra hsp hmem",
        unsat_solve_call_hyps="hx0 hx1 hx2 hx3 hx4 hra hsp hm_dmem'",
        unsat_rintro_cal="hcal",
        unsat_rintro_sp="hsp'",
    ),
}


@dataclass(frozen=True)
class ModulePreset:
    """Canonical configuration defaults for a known Kissat Lean module."""

    name: str
    prefix: str
    stem: str
    source_mod: str
    proof_mod: str
    hub_mod: str | None = None
    fns: str | None = None
    mod: str | None = None
    cert_name: str | None = None
    acyclic: str | None = None
    wf: str | None = None
    env: str | None = None
    spec_table: str | None = None
    spec_sigs: str | None = None
    module_ok: str | None = None
    no_exit: str | None = None
    entry_const: str = "Full.kissat_solve_bytes"
    entry_fn: str = "kissat_solve_bytes"
    entry_spec: str = "fullSolveBytesSpec"
    default_total_fns: int | None = None


MODULE_PRESETS: dict[str, ModulePreset] = {
    "FullM5": ModulePreset(
        name="FullM5",
        prefix="KissatM5",
        stem="m5",
        source_mod="LeanQbe.T.Examples.Kissat.FullM5",
        proof_mod="LeanQbe.T.Examples.Kissat.FullM5Proof",
        hub_mod="LeanQbe.T.Examples.Kissat.M5Hub",
        default_total_fns=DEFAULT_M5_TOTAL_FNS,
    ),
    "FullM4": ModulePreset(
        name="FullM4",
        prefix="KissatM4",
        stem="m4",
        source_mod="LeanQbe.T.Examples.Kissat.FullM4",
        proof_mod="LeanQbe.T.Examples.Kissat.FullM4Proof",
        hub_mod="LeanQbe.T.Examples.Kissat.M4Hub",
        default_total_fns=231,
    ),
    "FullM3": ModulePreset(
        name="FullM3",
        prefix="KissatM3",
        stem="m3",
        source_mod="LeanQbe.T.Examples.Kissat.FullM3",
        proof_mod="LeanQbe.T.Examples.Kissat.FullM3Proof",
        hub_mod="LeanQbe.T.Examples.Kissat.M3Hub",
        default_total_fns=204,
    ),
    "FullFast": ModulePreset(
        name="FullFast",
        prefix="KissatFast",
        stem="fast",
        source_mod="LeanQbe.T.Examples.Kissat.FullFast",
        proof_mod="LeanQbe.T.Examples.Kissat.FullFastProof",
        default_total_fns=196,
    ),
    "FullFastSched": ModulePreset(
        name="FullFastSched",
        prefix="KissatFastSched",
        stem="sched",
        source_mod="LeanQbe.T.Examples.Kissat.FullFastSched",
        proof_mod="LeanQbe.T.Examples.Kissat.FullFastSchedLemmas",
        fns="schedSplicedFns",
        mod="schedModule",
        wf="schedSplicedFns_wf",
        default_total_fns=173,
    ),
    "Full": ModulePreset(
        name="Full",
        prefix="KissatFull",
        stem="full",
        source_mod="LeanQbe.T.Examples.Kissat.Full",
        proof_mod="LeanQbe.T.Examples.Kissat.FullProof",
        default_total_fns=166,
    ),
    "Plain": ModulePreset(
        name="Plain",
        prefix="KissatPlain",
        stem="plain",
        source_mod="LeanQbe.T.Examples.Kissat.Plain",
        proof_mod="LeanQbe.T.Examples.Kissat.PlainLemmas",
        entry_const="kissat_solve_bytes",
        entry_spec="plainSolveBytesSpec",
        default_total_fns=59,
    ),
}

PRESET_ALIASES: dict[str, str] = {
    **{k.lower(): k for k in MODULE_PRESETS},
    "m5": "FullM5",
    "m4": "FullM4",
    "m3": "FullM3",
    "fast": "FullFast",
    "fastsched": "FullFastSched",
    "sched": "FullFastSched",
}


def resolve_preset(name: str) -> ModulePreset:
    """Resolve `--module` case-insensitively with concise alias support."""
    key = PRESET_ALIASES.get(name.strip().lower())
    if key is None:
        opts = ", ".join(MODULE_PRESETS)
        raise ValueError(f"unknown --module preset '{name}' (expected one of: {opts})")
    return MODULE_PRESETS[key]


@dataclass(frozen=True)
class SliceRange:
    """Inclusive-exclusive range `[start, start + count)` for one cert slice."""

    index: int
    start: int
    count: int

    @property
    def end(self) -> int:
        return self.start + self.count


@dataclass(frozen=True)
class FnMetric:
    """Per-function compilation complexity record used for slice balancing."""

    index: int
    name: str
    size: int
    loops: int
    groups: int
    calls: int
    cost: float
    source: str


@dataclass(frozen=True)
class LptSchedule:
    """Result of Longest-Processing-Time-first bin packing across workers."""

    workers: int
    loads: tuple[float, ...]
    bins: tuple[tuple[int, ...], ...]
    makespan: float
    mean_load: float
    max_mean_ratio: float


@dataclass(frozen=True)
class SliceStats:
    """Summary load statistics across slices and LPT workers."""

    num_slices: int
    raw_min: int
    raw_max: int
    raw_mean: float
    raw_max_mean: float
    cost_min: float
    cost_max: float
    cost_mean: float
    cost_max_mean: float
    lpt: LptSchedule
    singletons: tuple[tuple[int, str, int], ...]


@dataclass(frozen=True)
class CertConfig:
    """Resolved deterministic generation configuration."""

    prefix: str
    stem: str
    camel_prefix: str
    source_mod: str
    proof_mod: str
    hub_mod: str | None
    fns: str
    mod: str
    cert_name: str
    acyclic: str
    wf: str
    env: str
    spec_table: str
    spec_sigs: str
    module_ok: str
    no_exit: str
    entry_const: str
    entry_fn: str
    entry_spec: str
    entry_idx: int
    total_fns: int
    slices: tuple[SliceRange, ...]
    chunk_size: int
    max_dirs: int
    max_bound: int
    wrapper_mode: str
    print_axioms: bool
    fn_metrics: tuple[FnMetric, ...]
    before_stats: SliceStats
    after_stats: SliceStats


    @property
    def legal_sig(self) -> str:
        """Name of the generated `LegalSigAll` theorem."""
        return f"{self.stem}_legalSig"


def infer_stem(prefix: str) -> str:
    """Infer short stem (e.g. `KissatM4` -> `m4`, `KissatFast` -> `fast`)."""
    m = re.search(r"(M\d+)$", prefix)
    if m:
        return m.group(1).lower()
    if prefix.startswith("Kissat") and len(prefix) > 6:
        rest = prefix[6:]
        return rest[0].lower() + rest[1:]
    return prefix[0].lower() + prefix[1:]


def lower_camel(name: str) -> str:
    """Lowercase the initial character of a PascalCase identifier."""
    return name[0].lower() + name[1:] if name else name


def infer_source_mod(prefix: str, stem: str) -> str:
    """Infer canonical source module path under `LeanQbe.T.Examples.Kissat`."""
    if re.fullmatch(r"m\d+", stem):
        return f"LeanQbe.T.Examples.Kissat.Full{stem.upper()}"
    suffix = prefix[6:] if prefix.startswith("Kissat") and len(prefix) > 6 else prefix
    return f"LeanQbe.T.Examples.Kissat.{suffix}"


def detect_total_fns(root: Path, source_mod: str, fns: str) -> int | None:
    """Read `<fns>.length = N` from `source_mod`'s `.lean` file if present."""
    src_path = root / Path(*source_mod.split(".")).with_suffix(".lean")
    if not src_path.is_file():
        return None
    text = src_path.read_text(encoding="utf-8")
    pat = re.compile(rf"\b{re.escape(fns)}\.length\s*=\s*(\d+)\b")
    m = pat.search(text)
    return int(m.group(1)) if m else None


def compute_fn_cost(size: int, loops: int, groups: int, calls: int) -> float:
    """Estimate kernel WHNF + regalloc cost from IR/C0 size and control flow."""
    s = max(1, size)
    factor = 1.0 + 0.03 * loops + 0.004 * groups + 0.005 * calls
    return max(1.0, s * factor + 0.05 * (s ** 1.25))


def extract_c0_metrics(c_code: str) -> dict[str, dict[str, int | str]]:
    """Parse `kissat_c0!` C source strings into per-function structural metrics."""
    out: dict[str, dict[str, int | str]] = {}
    for fm in C_FN_HDR_RE.finditer(c_code):
        fn_name = fm.group(1)
        if fn_name in ("if", "while", "for", "switch", "else"):
            continue
        pos = fm.end()
        depth = 1
        while pos < len(c_code) and depth > 0:
            ch = c_code[pos]
            if ch == "{":
                depth += 1
            elif ch == "}":
                depth -= 1
            pos += 1
        body = c_code[fm.start() : pos]
        stmts = body.count(";")
        loops = len(re.findall(r"\b(?:for|while)\b", body))
        branches = len(re.findall(r"\b(?:if|else|case|switch)\b", body))
        calls = max(
            0, len(re.findall(r"\b(?:full|kissat|plain|solver)_[a-zA-Z0-9_]+\s*\(", body)) - 1
        )
        toks = len(
            re.findall(
                r"[A-Za-z_][A-Za-z0-9_]*|\d+|==|!=|<=|>=|&&|\|\||[+\-*/%&|^<>!;(){}]",
                body,
            )
        )
        est = max(10, int(round(12 + 0.65 * toks + 3.0 * stmts + 12.0 * loops + 6.0 * branches)))
        out[fn_name] = {
            "name": fn_name,
            "size": est,
            "loops": loops,
            "groups": branches + loops + 1,
            "calls": calls,
        }
    return out


def _strip_lean_comments(text: str) -> str:
    """Remove Lean block and line comments for static `List Fn` expression parsing."""
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    return re.sub(r"--[^\n]*", "", text)


def _unwrap_parens(expr: str) -> str:
    """Strip balanced outer parentheses around an expression."""
    p = expr.strip()
    while p.startswith("(") and p.endswith(")"):
        depth = 0
        balanced = True
        for idx, ch in enumerate(p):
            if ch in "([⟨":
                depth += 1
            elif ch in ")]⟩":
                depth -= 1
                if depth == 0 and idx < len(p) - 1:
                    balanced = False
                    break
        if not balanced or depth != 0:
            break
        p = p[1:-1].strip()
    return p


def _split_top_level(expr: str, sep: str) -> list[str]:
    """Split `expr` by separator `sep` outside brackets/angle-brackets."""
    parts: list[str] = []
    depth = 0
    i = 0
    start = 0
    while i < len(expr):
        ch = expr[i]
        if ch in "([⟨":
            depth += 1
        elif ch in ")]⟩":
            depth = max(0, depth - 1)
        elif depth == 0 and expr.startswith(sep, i):
            parts.append(expr[start:i])
            i += len(sep)
            start = i
            continue
        i += 1
    parts.append(expr[start:])
    return parts


def _scan_kissat_sources(
    kissat_dir: Path,
) -> tuple[
    dict[str, dict[str, int | str]],
    dict[str, list[tuple[str, str]]],
    dict[str, str],
    dict[str, tuple[str, str]],
]:
    """Collect C0 body metrics, `<pfx>_fns` literals, `List Fn` defs, and `Fn` aliases."""
    c_metrics: dict[str, dict[str, int | str]] = {}
    list_literals: dict[str, list[tuple[str, str]]] = {}
    list_exprs: dict[str, str] = {}
    fn_aliases: dict[str, tuple[str, str]] = {}

    if not kissat_dir.is_dir():
        return c_metrics, list_literals, list_exprs, fn_aliases

    for lean_file in sorted(kissat_dir.glob("*.lean")):
        txt = lean_file.read_text(encoding="utf-8")
        mod_short = lean_file.stem
        for m in C0_BLOCK_RE.finditer(txt):
            pfx, c_code = m.group(1), m.group(2)
            met = extract_c0_metrics(c_code)
            c_metrics.update(met)
            pairs = [(n, n) for n in met]
            list_literals[f"{pfx}_fns"] = pairs
            list_literals[f"{mod_short}.{pfx}_fns"] = pairs
            for n in met:
                fn_aliases[n] = (n, n)
                fn_aliases[f"{mod_short}.{n}"] = (n, n)
                if mod_short in ("Dimacs", "Full", "Full1", "Full2", "Full3"):
                    fn_aliases[f"Full.{n}"] = (n, n)

        clean = _strip_lean_comments(txt)
        for dm in re.finditer(
            r"(?:def|private\s+def|abbrev)\s+(\w+)\s*:\s*Fn\s*:=\s*(.*?)"
            r"(?=\n(?:def|private|theorem|end|@|/-))",
            clean,
            re.S,
        ):
            lhs, rhs = dm.group(1), dm.group(2)
            m_nm = re.search(r'"([a-zA-Z0-9_]+)"', rhs)
            m_bdy = re.search(r"\b((?:full|kissat|plain)_[a-zA-Z0-9_]+?)_body\b", rhs)
            src_nm = m_bdy.group(1) if m_bdy else (m_nm.group(1) if m_nm else lhs)
            out_nm = m_nm.group(1) if m_nm else src_nm
            fn_aliases[lhs] = (out_nm, src_nm)
            fn_aliases[f"{mod_short}.{lhs}"] = (out_nm, src_nm)

        for lm in re.finditer(
            r"(?:def|private\s+def|abbrev)\s+(\w+)\s*:\s*List\s+Fn\s*:=\s*(.*?)"
            r"(?=\n(?:def|private|theorem|end|@|/\-))",
            clean,
            re.S,
        ):
            lhs, rhs = lm.group(1), lm.group(2)
            list_exprs.setdefault(lhs, rhs)
            list_exprs[f"{mod_short}.{lhs}"] = rhs

    return c_metrics, list_literals, list_exprs, fn_aliases


def _eval_fn_lists(
    target_key: str,
    list_literals: dict[str, list[tuple[str, str]]],
    list_exprs: dict[str, str],
    fn_aliases: dict[str, tuple[str, str]],
) -> list[tuple[str, str]]:
    """Statically evaluate `++`, `.take`, `.drop`, `[..]` over parsed `List Fn` defs."""
    memo: dict[str, list[tuple[str, str]]] = {}

    def eval_fn_item(item: str) -> tuple[str, str]:
        s = item.strip()
        m_lit = re.match(r'^⟨"([^"]+)"\s*,.*?,\s*([A-Za-z0-9_.]+)_body\s*⟩$', s, re.S)
        if m_lit:
            return (m_lit.group(1), m_lit.group(2).split(".")[-1])
        if s in fn_aliases:
            return fn_aliases[s]
        short = s.split(".")[-1]
        return fn_aliases.get(short, (short, short))

    def eval_list(key: str, seen: set[str]) -> list[tuple[str, str]]:
        if key in memo:
            return memo[key]
        if key in list_literals:
            return list_literals[key]
        short = key.split(".")[-1]
        resolved_key = key if key in list_exprs else (short if short in list_exprs else "")
        if not resolved_key:
            return list_literals.get(short, [])
        if resolved_key in seen:
            return []
        next_seen = seen | {resolved_key}
        out: list[tuple[str, str]] = []
        for part in _split_top_level(list_exprs[resolved_key].strip(), "++"):
            out.extend(eval_expr(part, next_seen))
        memo[key] = out
        return out

    def eval_expr(expr: str, seen: set[str]) -> list[tuple[str, str]]:
        p = _unwrap_parens(expr)
        if p.startswith("[") and p.endswith("]"):
            inner = p[1:-1].strip()
            if not inner:
                return []
            return [eval_fn_item(it) for it in _split_top_level(inner, ",") if it.strip()]
        m_take = re.match(r"^(.*)\.take\s+(\d+)$", p, re.S)
        if m_take:
            return eval_expr(m_take.group(1), seen)[: int(m_take.group(2))]
        m_drop = re.match(r"^(.*)\.drop\s+(\d+)$", p, re.S)
        if m_drop:
            return eval_expr(m_drop.group(1), seen)[int(m_drop.group(2)) :]
        if "::" in p and "[" not in p:
            head, tail = p.split("::", 1)
            return [eval_fn_item(head)] + eval_expr(tail, seen)
        return eval_list(p, seen)

    return eval_list(target_key, set())


def _synthesize_m5_fn_pairs(
    m4_pairs: list[tuple[str, str]],
    kissat_dir: Path,
    total_fns: int | None,
) -> list[tuple[str, str]]:
    """Build ordered M5 function pairs from M4 baseline + `FullM5*.lean` C0 modules."""
    overrides: dict[str, str] = {}
    new_helpers: list[tuple[str, str]] = []
    m4_names = {out_nm for out_nm, _ in m4_pairs}
    for m5_file in sorted(kissat_dir.glob("FullM5*.lean")):
        if "Proof" in m5_file.name or "Lemmas" in m5_file.name:
            continue
        for m in C0_BLOCK_RE.finditer(m5_file.read_text(encoding="utf-8")):
            for nm in extract_c0_metrics(m.group(2)):
                base = nm[:-3] if nm.endswith("_m5") else nm
                if base in m4_names:
                    overrides[base] = nm
                else:
                    new_helpers.append((nm, nm))

    pairs = [(out_nm, overrides.get(out_nm, src_nm)) for out_nm, src_nm in m4_pairs]
    insert_at = max(0, len(pairs) - 1)  # Keep `kissat_solve_bytes` as final entry.
    combined = pairs[:insert_at] + new_helpers + pairs[insert_at:]
    if total_fns is None or total_fns == len(combined):
        return combined
    if total_fns < len(combined):
        if total_fns <= 1:
            return combined[-total_fns:]
        return combined[: total_fns - 1] + [combined[-1]]
    extra = total_fns - len(combined)
    pads = [(f"m5_ext_{k}", f"m5_ext_{k}") for k in range(extra)]
    return combined[:-1] + pads + [combined[-1]]


def resolve_static_metrics(
    root: Path,
    source_mod: str,
    fns_sym: str,
    total_fns: int,
    stem: str,
) -> tuple[FnMetric, ...]:
    """Estimate per-function compilation metrics from Lean/C0 sources without Lean."""
    kissat_dir = root / "LeanQbe" / "T" / "Examples" / "Kissat"
    c_metrics, list_literals, list_exprs, fn_aliases = _scan_kissat_sources(kissat_dir)
    src_short = source_mod.split(".")[-1]
    fn_pairs = _eval_fn_lists(f"{src_short}.{fns_sym}", list_literals, list_exprs, fn_aliases)

    if not fn_pairs and stem == "m5":
        m4_pairs = _eval_fn_lists("FullM4.m4Fns", list_literals, list_exprs, fn_aliases)
        if m4_pairs:
            fn_pairs = _synthesize_m5_fn_pairs(m4_pairs, kissat_dir, total_fns)

    if len(fn_pairs) != total_fns:
        # Synthetic fallback when source file is unavailable or partially spliced.
        if len(fn_pairs) > total_fns:
            fn_pairs = fn_pairs[: total_fns - 1] + [fn_pairs[-1]] if total_fns > 1 else fn_pairs[:1]
        elif fn_pairs:
            extra = total_fns - len(fn_pairs)
            pads = [(f"{stem}_fn_{i}", f"{stem}_fn_{i}") for i in range(extra)]
            fn_pairs = fn_pairs[:-1] + pads + [fn_pairs[-1]]
        else:
            fn_pairs = [(f"{stem}_fn_{i}", f"{stem}_fn_{i}") for i in range(total_fns)]

    out: list[FnMetric] = []
    for idx, (out_name, src_name) in enumerate(fn_pairs):
        met = c_metrics.get(src_name) or c_metrics.get(out_name)
        if met is not None:
            size = int(met["size"])
            loops = int(met["loops"])
            groups = int(met["groups"])
            calls = int(met["calls"])
            src_tag = "c0-static"
        else:
            size = 90
            loops = 1
            groups = 4
            calls = 1
            src_tag = "synthetic"
        out.append(
            FnMetric(
                index=idx,
                name=out_name,
                size=size,
                loops=loops,
                groups=groups,
                calls=calls,
                cost=compute_fn_cost(size, loops, groups, calls),
                source=src_tag,
            )
        )
    return tuple(out)


def load_profile_json(profile_path: Path) -> tuple[FnMetric, ...]:
    """Load per-function complexity metrics from a Lean probe JSON profile."""
    raw = json.loads(profile_path.read_text(encoding="utf-8"))
    if isinstance(raw, dict):
        if "functions" in raw:
            rows = raw["functions"]
        elif "fns" in raw:
            rows = raw["fns"]
        else:
            rows = [{"name": k, **v} if isinstance(v, dict) else {"name": k, "cost": v}
                    for k, v in raw.items()]
    elif isinstance(raw, list):
        rows = raw
    else:
        raise ValueError(f"unsupported JSON structure in --profile {profile_path}")

    if not rows:
        raise ValueError(f"empty profile list in --profile {profile_path}")

    metrics: list[FnMetric] = []
    for idx, row in enumerate(rows):
        if not isinstance(row, dict):
            raise ValueError(f"profile entry {idx} in {profile_path} must be a JSON object")
        fn_idx = int(row.get("index", idx))
        name = str(row.get("name", f"fn_{fn_idx}"))
        size = int(
            row.get(
                "mid_tflat_size",
                row.get(
                    "tflat_size",
                    row.get("inl_tflat_size", row.get("raw_size", row.get("size", 80))),
                ),
            )
        )
        loops = int(row.get("mid_loops", row.get("loops", row.get("raw_loops", 0))))
        groups = int(row.get("mid_groups", row.get("groups", row.get("raw_groups", 1))))
        calls = int(row.get("mid_calls", row.get("calls", row.get("raw_calls", 0))))
        explicit = row.get("cost", row.get("weight"))
        cost = float(explicit) if explicit is not None else compute_fn_cost(size, loops, groups, calls)
        metrics.append(
            FnMetric(
                index=fn_idx,
                name=name,
                size=size,
                loops=loops,
                groups=groups,
                calls=calls,
                cost=max(1.0, cost),
                source="profile-json",
            )
        )
    metrics.sort(key=lambda m: m.index)
    return tuple(metrics)


def lpt_pack(weights: list[float], workers: int) -> LptSchedule:
    """Assign slice weights to `workers` parallel workers using LPT bin packing."""
    if workers <= 0:
        raise ValueError(f"workers must be positive, got {workers}")
    w = min(workers, max(1, len(weights)))
    loads = [0.0] * w
    bins: list[list[int]] = [[] for _ in range(w)]
    for slice_idx, weight in sorted(enumerate(weights), key=lambda kv: (-kv[1], kv[0])):
        target_w = min(range(w), key=lambda i: (loads[i], i))
        loads[target_w] += weight
        bins[target_w].append(slice_idx)
    makespan = max(loads) if loads else 0.0
    mean_load = (sum(loads) / w) if w else 0.0
    ratio = (makespan / mean_load) if mean_load > 0 else 1.0
    return LptSchedule(
        workers=w,
        loads=tuple(loads),
        bins=tuple(tuple(b) for b in bins),
        makespan=makespan,
        mean_load=mean_load,
        max_mean_ratio=ratio,
    )


def classify_stragglers(
    metrics: tuple[FnMetric, ...],
    heavy_thresh: float | None = None,
) -> tuple[list[bool], list[bool]]:
    """Tag extreme singleton stragglers and heavy-family functions requiring isolation."""
    n = len(metrics)
    sorted_costs = sorted(m.cost for m in metrics)
    p90 = sorted_costs[min(n - 1, int(0.90 * n))]
    p95 = sorted_costs[min(n - 1, int(0.95 * n))]
    singleton_floor = heavy_thresh if heavy_thresh is not None else max(780.0, p95 * 1.45, p90 * 2.0)

    is_singleton: list[bool] = []
    is_heavy: list[bool] = []
    for m in metrics:
        sing = (m.cost >= singleton_floor) or (
            bool(SINGLETON_STRAGGLER_RE.match(m.name)) and m.cost >= max(220.0, p90 * 0.75)
        )
        heavy = sing or (m.cost >= max(p90 * 1.15, singleton_floor * 0.65)) or (
            bool(HEAVY_FAMILY_RE.match(m.name)) and m.cost >= max(180.0, p90 * 0.90)
        )
        is_singleton.append(sing)
        is_heavy.append(heavy)
    return is_singleton, is_heavy


def autobalance_slices(
    metrics: tuple[FnMetric, ...],
    slice_size: int = MAX_SLICE_SIZE,
    workers: int = DEFAULT_WORKERS,
    target_slices: int | None = None,
    heavy_thresh: float | None = None,
    file_overhead: float = DEFAULT_FILE_OVERHEAD,
) -> tuple[SliceRange, ...]:
    """Partition `[0, N)` into balanced `<= slice_size` contiguous cert slices.

    Combines straggler isolation (critical stragglers in singletons/small chunks,
    leaf functions packed tightly up to `slice_size`) with exact DP partitioning
    and LPT (`Longest-Processing-Time-first`) worker makespan selection.
    """
    n = len(metrics)
    if n == 0:
        raise ValueError("cannot balance 0 functions")
    if not 1 <= slice_size <= MAX_SLICE_SIZE:
        raise ValueError(f"slice_size must be in [1, {MAX_SLICE_SIZE}], got {slice_size}")

    is_sing, is_heavy = classify_stragglers(metrics, heavy_thresh=heavy_thresh)
    costs = [m.cost for m in metrics]
    pref = [0.0] * (n + 1)
    for i, c in enumerate(costs):
        pref[i + 1] = pref[i] + c

    def dp_partition(
        budget: float,
        allow_co_heavy: bool = False,
        enforce_sing: bool = True,
    ) -> list[tuple[int, int]] | None:
        inf_pen = 1e18
        dp_cnt = [10**9] * (n + 1)
        dp_pen = [inf_pen] * (n + 1)
        dp_prev = [-1] * (n + 1)
        dp_cnt[0] = 0
        dp_pen[0] = 0.0
        target = budget * 0.86
        for j in range(1, n + 1):
            lo_i = max(0, j - slice_size)
            for i in range(j - 1, lo_i - 1, -1):
                cnt = j - i
                if cnt > 1:
                    if enforce_sing and any(is_sing[i:j]):
                        break
                    if not allow_co_heavy and sum(1 for k in range(i, j) if is_heavy[k]) > 1:
                        break
                chunk_cost = file_overhead + (pref[j] - pref[i])
                if cnt > 1 and chunk_cost > budget:
                    break
                cand_cnt = dp_cnt[i] + 1
                cand_pen = dp_pen[i] + (chunk_cost - target) ** 2
                if cand_cnt < dp_cnt[j] or (cand_cnt == dp_cnt[j] and cand_pen < dp_pen[j]):
                    dp_cnt[j] = cand_cnt
                    dp_pen[j] = cand_pen
                    dp_prev[j] = i
        if dp_prev[n] < 0:
            return None
        ranges: list[tuple[int, int]] = []
        cur = n
        while cur > 0:
            prv = dp_prev[cur]
            ranges.append((prv, cur))
            cur = prv
        ranges.reverse()
        return ranges

    max_single = max(costs) + file_overhead
    chosen: list[tuple[int, int]] | None = None

    if target_slices is not None:
        if target_slices <= 0:
            raise ValueError(f"target_slices must be positive, got {target_slices}")
        min_possible = math.ceil(n / slice_size)
        eff_target = min(n, max(target_slices, min_possible))
        total_hi = sum(costs) + n * file_overhead
        for enforce_sing, co_heavy in ((True, False), (True, True), (False, True)):
            hi_rs = dp_partition(total_hi, allow_co_heavy=co_heavy, enforce_sing=enforce_sing)
            if hi_rs is None or len(hi_rs) > eff_target:
                continue
            lo = max(file_overhead + 1.0, max_single * 0.4)
            hi = total_hi
            best_rs = hi_rs
            for _ in range(42):
                mid_b = 0.5 * (lo + hi)
                cand = dp_partition(mid_b, allow_co_heavy=co_heavy, enforce_sing=enforce_sing)
                if cand is not None and len(cand) <= eff_target:
                    best_rs = cand
                    hi = mid_b
                else:
                    lo = mid_b
            chosen = list(best_rs)
            while len(chosen) < eff_target:
                split_candidates = [
                    (file_overhead + (pref[e] - pref[s]), idx)
                    for idx, (s, e) in enumerate(chosen)
                    if e - s > 1
                ]
                if not split_candidates:
                    break
                _, spl_idx = max(split_candidates)
                s, e = chosen[spl_idx]
                best_k = min(
                    range(s + 1, e),
                    key=lambda k: max(
                        file_overhead + (pref[k] - pref[s]),
                        file_overhead + (pref[e] - pref[k]),
                    ),
                )
                chosen[spl_idx : spl_idx + 1] = [(s, best_k), (best_k, e)]
            break

    if chosen is None:
        best_score: float | None = None
        soft_max_slices = max(24, math.ceil(n / 7.5))
        for frac in (0.85, 0.95, 1.0, 1.05, 1.12, 1.22, 1.32, 1.45, 1.75):
            budget = max_single * frac
            cand = dp_partition(budget, allow_co_heavy=False)
            if cand is None:
                continue
            weights = [file_overhead + (pref[e] - pref[s]) for s, e in cand]
            mean_w = sum(weights) / len(weights)
            chunk_ratio = max(weights) / mean_w if mean_w > 0 else 1.0
            sched = lpt_pack(weights, workers)
            # Balance per-slice max/mean and LPT worker makespan without over-fragmenting.
            k_reg = max(0, len(cand) - soft_max_slices) * 0.03
            score = chunk_ratio * (1.0 + 0.5 * (sched.max_mean_ratio - 1.0)) + k_reg
            if best_score is None or score < best_score:
                best_score = score
                chosen = cand
        if chosen is None:
            chosen = dp_partition(sum(costs) + n * file_overhead, allow_co_heavy=True)
            assert chosen is not None

    return tuple(
        SliceRange(index=idx, start=s, count=e - s)
        for idx, (s, e) in enumerate(chosen, start=1)
    )


def compute_slice_stats(
    metrics: tuple[FnMetric, ...],
    slices: tuple[SliceRange, ...],
    workers: int = DEFAULT_WORKERS,
    file_overhead: float = DEFAULT_FILE_OVERHEAD,
) -> SliceStats:
    """Compute raw-size and weighted-cost imbalance metrics plus LPT schedule."""
    raw_sums = [sum(metrics[k].size for k in range(sl.start, sl.end)) for sl in slices]
    cost_sums = [
        file_overhead + sum(metrics[k].cost for k in range(sl.start, sl.end))
        for sl in slices
    ]
    raw_mean = sum(raw_sums) / len(raw_sums)
    cost_mean = sum(cost_sums) / len(cost_sums)
    lpt = lpt_pack(cost_sums, workers)
    singletons = tuple(
        (sl.start, metrics[sl.start].name, metrics[sl.start].size)
        for sl in slices
        if sl.count == 1
    )
    return SliceStats(
        num_slices=len(slices),
        raw_min=min(raw_sums),
        raw_max=max(raw_sums),
        raw_mean=raw_mean,
        raw_max_mean=(max(raw_sums) / raw_mean) if raw_mean > 0 else 1.0,
        cost_min=min(cost_sums),
        cost_max=max(cost_sums),
        cost_mean=cost_mean,
        cost_max_mean=(max(cost_sums) / cost_mean) if cost_mean > 0 else 1.0,
        lpt=lpt,
        singletons=singletons,
    )


def compute_slices(
    total_fns: int,
    slice_size: int,
    explicit_sizes: list[int] | None,
) -> tuple[SliceRange, ...]:
    """Compute validated `<= 12`-fn slice ranges covering `[0, total_fns)`."""
    if total_fns <= 0:
        raise ValueError(f"total_fns must be positive, got {total_fns}")
    if not 1 <= slice_size <= MAX_SLICE_SIZE:
        raise ValueError(
            f"slice_size must be in [1, {MAX_SLICE_SIZE}], got {slice_size}"
        )

    if explicit_sizes is not None:
        sizes = explicit_sizes
        if any(not 1 <= s <= MAX_SLICE_SIZE for s in sizes):
            raise ValueError(
                f"every explicit slice size must be in [1, {MAX_SLICE_SIZE}]: {sizes}"
            )
        if sum(sizes) != total_fns:
            raise ValueError(
                f"sum(slice_sizes) = {sum(sizes)} != total_fns = {total_fns}"
            )
    else:
        sizes = []
        rem = total_fns
        while rem > 0:
            take = min(slice_size, rem)
            sizes.append(take)
            rem -= take

    out: list[SliceRange] = []
    pos = 0
    for idx, count in enumerate(sizes, start=1):
        out.append(SliceRange(index=idx, start=pos, count=count))
        pos += count
    return tuple(out)


def worst_case_axiom_len(ns: str, const_name: str) -> int:
    """Return worst-case char length of Lean's std3 `#print axioms` output line."""
    return len(ns) + len(const_name) + AXIOM_REPORT_FIXED_OVERHEAD


def render_axiom_prints(ns: str, direct_names: list[str]) -> list[str]:
    """Emit `#print axioms` lines only when their std3 output fits `< 115c`."""
    out: list[str] = []
    for name in direct_names:
        if worst_case_axiom_len(ns, name) > MAX_AXIOM_REPORT_LEN:
            raise ValueError(
                f"#print axioms {ns}.{name} would exceed {MAX_AXIOM_REPORT_LEN}c "
                f"({worst_case_axiom_len(ns, name)}c)"
            )
        out.append(f"#print axioms {name}")
    return out


def validate_generated_files(files: list[tuple[str, str]]) -> None:
    """Enforce repository Lean invariants across all generated module sources."""
    for rel_path, content in files:
        lines = content.splitlines()
        if len(lines) > MAX_FILE_LINES:
            raise ValueError(
                f"{rel_path} exceeds {MAX_FILE_LINES} LOC ({len(lines)} lines)"
            )
        first_nonempty = next((ln.strip() for ln in lines if ln.strip()), "")
        if first_nonempty != "module":
            raise ValueError(f"{rel_path}: first non-empty line must be 'module'")
        if "set_option autoImplicit false" not in content:
            raise ValueError(f"{rel_path}: missing 'set_option autoImplicit false'")
        ns_match = re.search(r"^namespace\s+([A-Za-z0-9_.]+)", content, re.M)
        ns = ns_match.group(1) if ns_match else ""
        for lineno, line in enumerate(lines, start=1):
            if len(line) > MAX_LINE_LEN:
                raise ValueError(
                    f"{rel_path}:{lineno} exceeds {MAX_LINE_LEN}c ({len(line)}c): {line}"
                )
            if re.match(r"^\s*import\s+all\b", line):
                raise ValueError(
                    f"{rel_path}:{lineno}: forbidden 'import all' in generated cert module"
                )
            m_ax = re.match(r"^\s*#print\s+axioms\s+([A-Za-z0-9_.]+)\s*$", line)
            if m_ax:
                sym = m_ax.group(1)
                # Compute exact report length for either relative or qualified identifier.
                report_len = (
                    len(sym) + AXIOM_REPORT_FIXED_OVERHEAD
                    if "." in sym or not ns
                    else worst_case_axiom_len(ns, sym)
                )
                if report_len > MAX_AXIOM_REPORT_LEN:
                    raise ValueError(
                        f"{rel_path}:{lineno}: #print axioms {sym} worst-case output "
                        f"{report_len}c > {MAX_AXIOM_REPORT_LEN}c"
                    )


def check_line_lengths(rel_path: str, content: str) -> None:
    """Assert every line in generated Lean output fits within `MAX_LINE_LEN`."""
    for lineno, line in enumerate(content.splitlines(), start=1):
        if len(line) > MAX_LINE_LEN:
            raise ValueError(
                f"{rel_path}:{lineno} exceeds {MAX_LINE_LEN}c ({len(line)}c): {line}"
            )


def fmt_max_bound_opt(max_bound: int) -> str:
    """Return optional `(maxBound := ...)` argument when non-default."""
    return "" if max_bound == 2048 else f" (maxBound := {max_bound})"


def wrap_comment_lines(text: str, max_len: int = MAX_LINE_LEN) -> list[str]:
    """Wrap prose onto lines <= `max_len` at word boundaries without changing tokens."""
    words = text.split()
    out: list[str] = []
    cur = ""
    for w in words:
        cand = f"{cur} {w}" if cur else w
        if len(cand) <= max_len:
            cur = cand
        else:
            if cur:
                out.append(cur)
            cur = w
    if cur:
        out.append(cur)
    return out


def wrap_open_pairs(items: list[str]) -> list[str]:
    """Pack `open ...` module items cleanly within `MAX_LINE_LEN`."""
    lines: list[str] = []
    cur = "open"
    for item in items:
        cand = f"{cur} {item}"
        if len(cand) <= MAX_LINE_LEN:
            cur = cand
        else:
            lines.append(cur)
            cur = f"open {item}"
    if cur != "open":
        lines.append(cur)
    return lines


def render_bounds(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>Bounds.lean` using `eval_prefix_ext!`."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}Bounds"
    mb_opt = fmt_max_bound_opt(cfg.max_bound)
    eval_call = (
        f"eval_prefix_ext! {cfg.stem}AllExt {arch.targ} {arch.lt} "
        f"{cfg.fns}{mb_opt}"
    )
    if len(eval_call) > MAX_LINE_LEN:
        eval_call = (
            f"eval_prefix_ext! {cfg.stem}AllExt\n"
            f"  {arch.targ} {arch.lt} {cfg.fns}{mb_opt}"
        )

    hub_note = f" (hub `{cfg.hub_mod}`)" if cfg.hub_mod else ""
    lines = [
        "module",
        "",
        "public import LeanQbe.T.Main",
        f"public import {arch.targ_mod}",
        f"public import {cfg.source_mod}",
        "meta import Lean",
        "meta import LeanQbe.T.MainCertElab",
        f"meta import {arch.targ_mod}",
        f"meta import {cfg.source_mod}",
        "",
        "/-!",
        f"# {cfg.prefix} Auto-Computed Prefix Bounds on {arch.isa_title}",
        "",
        *wrap_comment_lines(
            f"Precomputes `(SigEntry × Nat)` stack bounds across all "
            f"`{cfg.total_fns}` functions of `{cfg.source_mod}.{cfg.fns}`"
            f"{hub_note} via `eval_prefix_ext!`, enabling flat 1-tier parallel "
            "slice certificates via `<prefix>ExtPrefix`."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "@[expose] public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(["LeanQbe.T", arch.ns_prefix, cfg.source_mod]),
        "",
        "-- Auto-computed reversed `(sig, bound)` accumulator for the full module.",
        eval_call,
        "",
        "/-- Exported callee signatures and stack bounds for prefix `[0, k)`. -/",
        f"def {cfg.stem}ExtPrefix (k : Nat) : List (SigEntry × Nat) :=",
        f"  {cfg.stem}AllExt.drop ({cfg.fns}.length - k)",
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_slice(cfg: CertConfig, arch: ArchSpec, sl: SliceRange) -> str:
    """Render `<Prefix>Cert<i>.lean` for one slice `<= 12` functions."""
    total_slices = len(cfg.slices)
    ns = f"{arch.ns_prefix}.{cfg.prefix}Cert{sl.index}"
    bounds_mod = f"{arch.ns_prefix}.{cfg.prefix}Bounds"
    uses_ext = sl.index > 1

    pub_imports = [
        "public import LeanQbe.T.MainCertCore",
        f"public import {arch.lemmas_mod}",
    ]
    if uses_ext:
        pub_imports.append(f"public import {bounds_mod}")
    pub_imports.append(f"public import {cfg.source_mod}")

    meta_imports = [
        "meta import Lean",
        "meta import LeanQbe.T.MainCertElab",
        f"meta import {arch.targ_mod}",
    ]
    if uses_ext:
        meta_imports.append(f"meta import {bounds_mod}")
    meta_imports.append(f"meta import {cfg.source_mod}")

    open_parts = ["LeanQbe.T", arch.ns_prefix]
    if uses_ext:
        open_parts.append(bounds_mod)
    open_parts.append(cfg.source_mod)

    if total_slices == 1:
        mod_rhs = cfg.fns
    elif sl.index == 1:
        mod_rhs = f"{cfg.fns}.take {sl.count}"
    elif sl.index == total_slices:
        mod_rhs = f"{cfg.fns}.drop {sl.start}"
    else:
        mod_rhs = f"({cfg.fns}.drop {sl.start}).take {sl.count}"

    mod_def = f"def slice{sl.index}Mod : Module := {{ fns := {mod_rhs} }}"
    if len(mod_def) > MAX_LINE_LEN:
        mod_def = (
            f"def slice{sl.index}Mod : Module :=\n"
            f"  {{ fns := {mod_rhs} }}"
        )

    ext_opt = f" (ext := {cfg.stem}ExtPrefix {sl.start})" if uses_ext else ""
    mb_opt = fmt_max_bound_opt(cfg.max_bound)
    cmd_head = (
        f"compile_linked_chunks! cert{sl.index} {arch.targ} {arch.layout} "
        f"{arch.lt} {arch.cl}"
    )
    cmd_tail = (
        f"  slice{sl.index}Mod {cfg.chunk_size}{ext_opt} "
        f"(maxDirs := {cfg.max_dirs}){mb_opt}"
    )
    if len(cmd_tail) > MAX_LINE_LEN:
        parts = [f"  slice{sl.index}Mod {cfg.chunk_size}"]
        if ext_opt:
            parts.append(f" {ext_opt.strip()}")
        parts.append(f" (maxDirs := {cfg.max_dirs}){mb_opt}")
        cmd_tail = "\n  ".join([parts[0], *[p.strip() for p in parts[1:]]])

    lines = [
        "module",
        "",
        *pub_imports,
        *meta_imports,
        "",
        "/-!",
        f"# {cfg.prefix} Certificate Slice {sl.index}/{total_slices} on "
        f"{arch.isa_title}",
        "",
        *wrap_comment_lines(
            f"Kernel-checked compilation cert (`cert{sl.index}`) for slice "
            f"`[{sl.start}, {sl.end})` (`{sl.count}` functions) of "
            f"`{cfg.source_mod}.{cfg.fns}` on `{arch.targ}`."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "@[expose] public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(open_parts),
        "",
        f"/-- Slice {sl.index} sub-module (`[{sl.start}, {sl.end})`, "
        f"`{sl.count}` functions). -/",
        mod_def,
        "",
        cmd_head,
        cmd_tail,
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_cert_ladder(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>Cert.lean` combining slices via `LinkedCert.append`."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}Cert"
    total_slices = len(cfg.slices)
    cert_ty = (
        f"LinkedCert {arch.targ} {arch.layout} {arch.lt} {arch.cl} "
        f"{{mod}} [] [] 0 {cfg.max_bound}"
    )

    pub_imports = [
        "public import LeanQbe.T.MainCertProof",
        *[
            f"public import {arch.ns_prefix}.{cfg.prefix}Cert{sl.index}"
            for sl in cfg.slices
        ],
    ]
    pub_imports.append(f"public import {cfg.source_mod}")

    slice_ns = [f"{arch.ns_prefix}.{cfg.prefix}Cert{sl.index}" for sl in cfg.slices]

    pref_mods: list[str] = []
    if total_slices >= 3:
        for sl in cfg.slices[1:-1]:
            doc = f"/-- Prefix sub-module `[0, {sl.end})`. -/"
            rhs = f"{cfg.fns}.take {sl.end}"
            defn = f"def pref{sl.index}Mod : Module := {{ fns := {rhs} }}"
            if len(defn) > MAX_LINE_LEN:
                defn = f"def pref{sl.index}Mod : Module :=\n  {{ fns := {rhs} }}"
            pref_mods.extend([doc, defn, ""])

    ladder_defs: list[str] = []
    if total_slices == 1:
        ty_full = cert_ty.format(mod=cfg.mod)
        ladder_defs.extend(
            [
                f"/-- Full kernel-checked cert covering `{cfg.total_fns}` "
                f"functions in `{cfg.mod}` on {arch.isa_title}. -/",
                f"noncomputable def {cfg.cert_name} :",
                f"    {ty_full} :=",
                "  cert1",
                "",
            ]
        )
    else:
        for sl in cfg.slices[1:]:
            is_first_step = sl.index == 2
            is_last_step = sl.index == total_slices
            lhs_cert = "cert1" if is_first_step else f"pref{sl.index - 1}Cert"
            rhs_cert = f"cert{sl.index}"
            def_name = cfg.cert_name if is_last_step else f"pref{sl.index}Cert"
            mod_name = cfg.mod if is_last_step else f"pref{sl.index}Mod"
            ty_line = cert_ty.format(mod=mod_name)

            if is_last_step:
                doc = (
                    f"/-- Full kernel-checked cert covering all "
                    f"`{cfg.total_fns}` functions in `{cfg.mod}` on "
                    f"{arch.isa_title}. -/"
                )
                proof = (
                    f"(by exact (List.take_append_drop {sl.start} "
                    f"{cfg.fns}).symm)"
                )
            else:
                doc = f"/-- Linked certificate for prefix `[0, {sl.end})`. -/"
                proof = (
                    f"(by exact List.take_add (l := {cfg.fns}) "
                    f"(i := {sl.start}) (j := {sl.count}))"
                )

            append_line = f"  {lhs_cert}.append {rhs_cert} {proof}"
            if len(append_line) > MAX_LINE_LEN:
                ladder_defs.extend(
                    [
                        doc,
                        f"noncomputable def {def_name} :",
                        f"    {ty_line} :=",
                        f"  {lhs_cert}.append {rhs_cert}",
                        f"    {proof}",
                        "    (by t_kernel_rfl)",
                        "",
                    ]
                )
            else:
                ladder_defs.extend(
                    [
                        doc,
                        f"noncomputable def {def_name} :",
                        f"    {ty_line} :=",
                        append_line,
                        "    (by t_kernel_rfl)",
                        "",
                    ]
                )

    axiom_lines: list[str] = []
    if cfg.print_axioms and worst_case_axiom_len(ns, cfg.cert_name) <= MAX_AXIOM_REPORT_LEN:
        axiom_lines = ["", *render_axiom_prints(ns, [cfg.cert_name])]

    lines = [
        "module",
        "",
        *pub_imports,
        "meta import Lean",
        f"meta import {arch.targ_mod}",
        f"meta import {cfg.source_mod}",
        "",
        "/-!",
        f"# {cfg.prefix} Native Compilation Certificate on {arch.isa_title}",
        "",
        *wrap_comment_lines(
            f"Combines all `{total_slices}` flat 1-tier slices "
            f"(`{cfg.prefix}Cert1`..`{cfg.prefix}Cert{total_slices}`) via "
            f"`LinkedCert.append` into `{cfg.cert_name}` over "
            f"`{cfg.source_mod}.{cfg.mod}` (`{cfg.total_fns}` functions)."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "@[expose] public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(["LeanQbe.T", arch.ns_prefix, cfg.source_mod]),
        *wrap_open_pairs(slice_ns),
        "",
        *pref_mods,
        *ladder_defs,
        *axiom_lines,
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_cert_link(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>CertLink.lean` with `legalSig`, `mk_module_fnspec`, `solve_*`."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}CertLink"
    cert_mod = f"{arch.ns_prefix}.{cfg.prefix}Cert"
    solve_name = f"solve_{arch.arch_tag}_of_fnspec"

    solve_sig_lines = [
        f"theorem {solve_name} {{b : Nat}}",
        "    {spec : Spec [i64, i64, i64, i64, i64] [i64]}",
        f"    (hfnspec : {arch.targ}.FnSpec hh \"{cfg.entry_fn}\" spec b 0)",
        "    (cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64)",
        "    {m : Mem 64} {Q : Post [i64]}",
        "    (hspec : spec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q",
        "      (fun _ _ _ _ => False))",
        "    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)",
        *arch.solve_link_hyps,
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        *arch.callee_saved_pred,
        f"        {arch.sp_ret} ∧",
        f"        ∃ m', Q ({arch.ret_reg}, ()) m' ∧",
        "          (st.data.dmem =⋆ Eq m' ⋆",
        *arch.solve_stack_post,
        f"      ⟨s, Labels.label \"{cfg.entry_fn}\"⟩",
    ]
    solve_block = [
        f"/-- Lifting any `FnSpec` for `\"{cfg.entry_fn}\"` at stack bound "
        "`b` and contract",
        f"`spec` to {arch.kraken_isa} `Eventually` via `{arch.of_returns_fn}`. -/",
        *solve_sig_lines[:-1],
        f"{solve_sig_lines[-1]} := by",
        f"  have hargs : {arch.targ}.ArgsIn (as := [i64, i64, i64, i64, i64])",
        "      (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) s :=",
        "    ⟨_, rfl,",
        *arch.solve_hargs_chain,
        "  refine eventually_weaken _ _ _ _ ?_",
        f"    ({arch.of_returns_fn} hfnspec hspec s ra R hargs {arch.of_returns_args})",
        f"  rintro st ⟨hpc, {arch.solve_rintro_cal}, hsp', rets, m', hQ, hrets, hm'⟩",
        "  rcases rets with ⟨r, ⟨⟩⟩",
        *arch.rets_extract_lines,
        f"  exact ⟨hpc, {arch.solve_rintro_cal}, hsp', m', hQ, hm'⟩",
    ]

    # Single-line `< 115c` axiom audit: alias `solve_*_of_fnspec` when needed.
    axiom_section: list[str] = []
    if cfg.print_axioms:
        audit_names: list[str] = []
        for cand in (cfg.legal_sig, "mk_module_fnspec"):
            if worst_case_axiom_len(ns, cand) <= MAX_AXIOM_REPORT_LEN:
                audit_names.append(cand)
        if worst_case_axiom_len(ns, solve_name) <= MAX_AXIOM_REPORT_LEN:
            audit_names.append(solve_name)
        elif worst_case_axiom_len(ns, "ax_solve") <= MAX_AXIOM_REPORT_LEN:
            solve_alias_sig = [
                solve_sig_lines[0].replace(f"theorem {solve_name}", "theorem ax_solve"),
                *solve_sig_lines[1:-1],
                f"{solve_sig_lines[-1]} :=",
                f"  {solve_name} hfnspec cnf_ptr cnf_len work_ptr work_len fuel",
                f"    hspec s ra R {arch.solve_call_hyps}",
            ]
            solve_block.extend(["", *solve_alias_sig])
            audit_names.append("ax_solve")
        if audit_names:
            axiom_section = ["", *render_axiom_prints(ns, audit_names)]

    lines = [
        "module",
        "",
        f"public import {cert_mod}",
        "import Kraken.Mem",
        "import Kraken.Separation",
        "",
        "/-!",
        f"# {cfg.prefix} Legal-Sig & Host Linking Helpers on {arch.isa_title}",
        "",
        *wrap_comment_lines(
            f"Exports `{cfg.legal_sig}`, `mk_module_fnspec`, and "
            f"`solve_{arch.arch_tag}_of_fnspec` over "
            f"`{cert_mod}.{cfg.cert_name}`."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "@[expose] public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(
            ["LeanQbe.T", arch.ns_prefix, cert_mod, cfg.source_mod, "Kraken"]
        ),
        "",
        f"private theorem {cfg.stem}_legalSig_check :",
        f"    checkLegalSigAll {arch.lt} {cfg.fns} = true := by",
        "  t_kernel_rfl",
        "",
        f"/-- All `{cfg.total_fns}` function signatures in `{cfg.fns}` satisfy "
        f"`{arch.lt}.legalSig`. -/",
        f"theorem {cfg.legal_sig} : LegalSigAll {arch.lt} {cfg.fns} :=",
        f"  legalSigAll_of_check {cfg.stem}_legalSig_check",
        "",
        "section Generic",
        "variable [hh : Host]",
        "",
        f"/-- Generic `FnSpec` for every function in `{cfg.mod}` on `{arch.targ}`, "
        "parameterized over a",
        "sound environment `Γ` whose contracts ignore exit continuations. -/",
        f"theorem mk_module_fnspec (Γ : Env)",
        f"    (hsound : ∀ f ∈ {cfg.fns}, ∀ args m Q X,",
        "      Γ f.name f.as f.rs args m Q X → Func.wp Γ f.body args m Q X)",
        f"    (hnoex : ∀ g ∈ {cfg.fns}, ∀ args m Q X X',",
        "      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')",
        f"    (k₀ : Nat) (hc : {cfg.cert_name}.code.IsInfixAt Host.prog k₀)",
        "    (hu : Host.LabelsUnique)",
        f"    {{f : Fn}} (hf : f ∈ {cfg.mod}.fns) :",
        f"    {arch.targ}.Defined hh f.name ∧",
        f"      {arch.targ}.FnSpec hh f.name (Γ f.name f.as f.rs) "
        f"({cfg.cert_name}.bound f.name) 0 :=",
        f"  {cfg.cert_name}.fnSpec_noExit_of_legalSigAll hh Γ k₀ hc hu",
        f"    {cfg.acyclic} {cfg.wf} {cfg.legal_sig} hsound hf (hnoex f hf)",
        "",
        *solve_block,
        "",
        "end Generic",
        *axiom_section,
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_top_wrapper(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>.lean` combining cert, link helpers, and proof (`0` `import all`)."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}"
    cert_mod = f"{arch.ns_prefix}.{cfg.prefix}Cert"
    link_mod = f"{arch.ns_prefix}.{cfg.prefix}CertLink"
    compiled_name = f"{cfg.camel_prefix}_compiled_{arch.arch_tag}"
    bound_suffix = "" if cfg.max_bound == 2048 else f" [] [] 0 {cfg.max_bound}"
    compiled_ty = (
        f"LinkedCert {arch.targ} {arch.layout} {arch.lt} {arch.cl} "
        f"{cfg.mod}{bound_suffix}"
    )
    if len(f"    {compiled_ty} :=") <= MAX_LINE_LEN:
        compiled_decl = [
            f"@[reducible] noncomputable def {compiled_name} :",
            f"    {compiled_ty} :=",
            f"  {cfg.prefix}Cert.{cfg.cert_name}",
        ]
    else:
        compiled_decl = [
            f"@[reducible] noncomputable def {compiled_name} :",
            f"    LinkedCert {arch.targ} {arch.layout} {arch.lt} {arch.cl}",
            f"      {cfg.mod}{bound_suffix} :=",
            f"  {cfg.prefix}Cert.{cfg.cert_name}",
        ]

    pub_imports = [
        f"public import {cert_mod}",
        f"public import {link_mod}",
    ]
    if cfg.wrapper_mode != "compiled":
        pub_imports.append(f"public import {cfg.proof_mod}")

    priv_imports: list[str] = [f"import {arch.lemmas_mod}"]
    if cfg.wrapper_mode == "full":
        priv_imports.extend(
            [
                "import LeanQbe.T.Logic.MemLemmas",
                "import Std.Sat.CNF.Basic",
            ]
        )
    priv_imports.extend(["import Kraken.Mem", "import Kraken.Separation"])

    open_parts = [
        "Std",
        "Std.Sat",
        "Std.ExtHashMap",
        "LeanQbe.T",
        "LeanQbe.T.Examples.Kissat",
        "LeanQbe.T.Examples.LratBytes",
        cfg.source_mod,
        arch.ns_prefix,
        link_mod,
        "Kraken",
    ]
    if cfg.wrapper_mode == "full" and cfg.entry_const.startswith("Full."):
        open_parts.append("LeanQbe.T.Examples.Kissat.Full")

    body: list[str] = [
        *wrap_comment_lines(
            f"/-- Compiled `LinkedCert` for `{cfg.mod}` (`{cfg.total_fns}` "
            f"functions) on {arch.isa_title}. -/"
        ),
        *compiled_decl,
        "",
    ]

    fnspec_thm = f"{cfg.stem}_module_fnspec"
    if cfg.wrapper_mode in ("fnspec", "full"):
        body.extend(
            [
                *wrap_comment_lines(
                    f"/-- Unconditional whole-module `Defined` + `FnSpec` for "
                    f"all `{cfg.total_fns}` functions in `{cfg.mod}` under "
                    f"`{cfg.env}` on {arch.isa_title}. -/"
                ),
                f"theorem {fnspec_thm} [hh : Host] (k₀ : Nat)",
                f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
                "    (hu : Host.LabelsUnique)",
                f"    {{f : Fn}} (hf : f ∈ {cfg.mod}.fns) :",
                f"    {arch.targ}.Defined hh f.name ∧",
                f"      {arch.targ}.FnSpec hh f.name ({cfg.env} f.name f.as f.rs)",
                f"        ({compiled_name}.bound f.name) 0 :=",
                f"  {cfg.prefix}CertLink.mk_module_fnspec {cfg.env}",
                "    (fun g hg args m Q X hs => by",
                "      obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg",
                f"      exact ({cfg.module_ok}.fnsOk pre g post hsp).2.2 args m Q X hs)",
                f"    (fun g _ => {cfg.no_exit} g.name g.as g.rs) k₀ hc hu hf",
                "",
            ]
        )

    unsat_audit: list[str] = []
    if cfg.wrapper_mode == "full":
        unsat_lines, unsat_audit = render_unsat_section(cfg, arch, compiled_name, ns)
        body.extend(
            [
                f"private theorem solve_in_{cfg.mod} :",
                f"    {cfg.entry_const} ∈ {cfg.mod}.fns := by",
                "  exact List.mem_of_getElem?",
                f"    (by t_kernel_rfl : ({cfg.mod}.fns)[{cfg.entry_idx}]? = "
                f"some {cfg.entry_const})",
                "",
                f"private theorem {cfg.stem}Env_names_eq",
                "    (spec : Spec [i64, i64, i64, i64, i64] [i64]) :",
                f"    ({cfg.spec_table} spec).map SpecEntry.name = "
                f"{cfg.fns}.map Fn.name := by",
                f"  have h := congrArg (List.map Prod.fst) ({cfg.spec_sigs} spec)",
                "  simp only [List.map_map] at h; exact h",
                "",
                f"private theorem {cfg.fns}_nodup : ({cfg.fns}.map Fn.name).Nodup :=",
                f"  (List.nodup_append.mp {cfg.module_ok}.nodup).1",
                "",
                f"private theorem {cfg.spec_table}_nodup",
                "    (spec : Spec [i64, i64, i64, i64, i64] [i64]) :",
                f"    (({cfg.spec_table} spec).map SpecEntry.name).Nodup :=",
                f"  Eq.mp (congrArg List.Nodup ({cfg.stem}Env_names_eq spec).symm) "
                f"{cfg.fns}_nodup",
                "",
                "private theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}",
                "    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by",
                "  have hm := sep_mono (Q := Q)",
                "    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h",
                "  rw [sep_ex_l] at hm",
                "  obtain ⟨m, hm'⟩ := hm",
                "  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩",
                "",
                *unsat_lines,
            ]
        )

    axiom_section: list[str] = []
    if cfg.print_axioms:
        audit_names: list[str] = []
        if worst_case_axiom_len(ns, compiled_name) <= MAX_AXIOM_REPORT_LEN:
            audit_names.append(compiled_name)
        if cfg.wrapper_mode in ("fnspec", "full") and (
            worst_case_axiom_len(ns, fnspec_thm) <= MAX_AXIOM_REPORT_LEN
        ):
            audit_names.append(fnspec_thm)
        audit_names.extend(unsat_audit)
        if audit_names:
            axiom_section = [*render_axiom_prints(ns, audit_names), ""]

    lines = [
        "module",
        "",
        *pub_imports,
        *priv_imports,
        "",
        "/-!",
        f"# {cfg.prefix} (`{cfg.total_fns}` fns) Unconditional {arch.isa_title} "
        "Theorems",
        "",
        *wrap_comment_lines(
            f"Combines `{cfg.prefix}Cert.{cfg.cert_name}` and "
            f"`{cfg.prefix}CertLink` with solver proof contracts."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "@[expose] public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(open_parts),
        "",
        *body,
        *axiom_section,
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_unsat_section(
    cfg: CertConfig, arch: ArchSpec, compiled_name: str, ns: str
) -> tuple[list[str], list[str]]:
    """Render zero-`import all` UNSAT soundness and answer-only wrappers."""
    unsat_thm = f"{cfg.stem}_solve_bytes_unsat_{arch.arch_tag}"
    sound_thm = f"{cfg.stem}_solve_bytes_unsat_sound_{arch.arch_tag}"
    entry_label = f"Labels.label \"{cfg.entry_fn}\""
    bound_expr = f"({compiled_name}.bound \"{cfg.entry_fn}\")"
    solve_name = f"solve_{arch.arch_tag}_of_fnspec"

    sound_ret = [
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        f"        ({arch.ret_reg} = 0#64 ∨",
        f"          {arch.ret_reg} = 10#64 ∨",
        f"          {arch.ret_reg} = 20#64) ∧",
        f"        ({arch.ret_reg} = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))",
        f"      ⟨s, {entry_label}⟩",
    ]

    lines = [
        "section Unsat",
        "",
        "variable [hh : Host] (k₀ : Nat)",
        f"  (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
        "  (hu : Host.LabelsUnique)",
        "  (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) "
        "(wlen : Nat)",
        "  (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)",
        "  (hwfit : work_ptr.toNat + wlen < 2 ^ 64)",
        "  (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)",
        *arch.unsat_reg_hyps(bound_expr),
        "include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit "
        "s ra R",
        f"  {arch.solve_call_hyps}",
        "",
        *wrap_comment_lines(
            f"/-- Unconditional end-to-end {arch.isa_title} UNSAT soundness "
            f"for `{cfg.mod}`. -/"
        ),
        f"theorem {unsat_thm} :",
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        f"        ({arch.ret_reg} = 0#64 ∨",
        f"          {arch.ret_reg} = 10#64 ∨",
        f"          {arch.ret_reg} = 20#64) ∧",
        f"        ({arch.ret_reg} = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
        *arch.callee_saved_pred,
        f"        {arch.sp_ret} ∧",
        *arch.unsat_st_dmem(bound_expr),
        f"      ⟨s, {entry_label}⟩ := by",
        f"  have hfn := ({cfg.stem}_module_fnspec k₀ hc hu "
        f"solve_in_{cfg.mod}).2",
        *arch.unsat_hm0(bound_expr),
        "    rw [← sep_assoc]; exact hmem",
        "  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0",
        *arch.unsat_hm_dmem(bound_expr),
        "    rw [sep_assoc]; exact hm_dmem",
        f"  have hspec : {cfg.env} \"{cfg.entry_fn}\" "
        "[i64, i64, i64, i64, i64] [i64]",
        "      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,",
        "        BitVec.ofNat 64 wlen, fuel, ()) m",
        "      (fun r m' =>",
        "        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧",
        "        (r.fst = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
        "        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')",
        "      (fun _ _ _ _ => False) :=",
        "    Env.ofTable_of_mem",
        f"      (List.mem_of_getElem? (rfl : "
        f"({cfg.spec_table} _)[{cfg.entry_idx}]? = some _))",
        f"      ({cfg.spec_table}_nodup {cfg.entry_spec})",
        "      ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit,",
        "        by rw [sep_emp]; exact hm_in,",
        "        fun _ _ h u' m' =>",
        "          by rw [sep_emp] at m'; exact ⟨h, u', m'⟩⟩",
        "  refine eventually_weaken _ _ _ _ ?_",
        f"    ({cfg.prefix}CertLink.{solve_name} hfn cnf_ptr _ "
        "work_ptr _ fuel",
        f"      hspec s ra R {arch.unsat_solve_call_hyps})",
        f"  rintro st ⟨hpc, {arch.unsat_rintro_cal}, {arch.unsat_rintro_sp}, "
        "m', ⟨hdom, hu', hm'⟩, hst⟩",
        "  rw [sep_assoc] at hst",
        "  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst",
        "  rw [← sep_assoc] at hst'",
        f"  exact ⟨hpc, hdom, hu', {arch.unsat_rintro_cal}, {arch.unsat_rintro_sp}, hst'⟩",
        "",
        *wrap_comment_lines(
            f"/-- Answer-only {arch.isa_title} UNSAT soundness corollary for "
            f"`{cfg.mod}`. -/"
        ),
        f"theorem {sound_thm} :",
        *sound_ret[:-1],
        f"{sound_ret[-1]} :=",
        "  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)",
        f"    ({unsat_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen "
        "hcfit hwfit",
        f"      s ra R {arch.solve_call_hyps})",
    ]
    call_args = (
        f"({sound_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen "
        "hcfit hwfit\n"
        f"    s ra R {arch.solve_call_hyps})"
    )

    audit_names: list[str] = []
    if worst_case_axiom_len(ns, unsat_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(unsat_thm)
    if worst_case_axiom_len(ns, sound_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(sound_thm)
    elif (
        cfg.print_axioms
        and worst_case_axiom_len(ns, "ax_unsat_sound") <= MAX_AXIOM_REPORT_LEN
    ):
        lines.extend(
            [
                "",
                "theorem ax_unsat_sound :",
                *sound_ret[:-1],
                f"{sound_ret[-1]} :=",
                f"  {call_args}",
            ]
        )
        audit_names.append("ax_unsat_sound")

    lines.extend(["", "end Unsat", ""])
    return lines, audit_names


def build_plan(cfg: CertConfig, arches: list[str]) -> list[tuple[str, str]]:
    """Build deterministic `(relative_path, lean_source)` pairs and validate invariants."""
    files: list[tuple[str, str]] = []
    for arch_key in arches:
        arch = ARCH_SPECS[arch_key]
        base = f"LeanQbe/T/{arch.dir_name}"
        planned: list[tuple[str, str]] = [
            (f"{base}/{cfg.prefix}Bounds.lean", render_bounds(cfg, arch)),
        ]
        for sl in cfg.slices:
            planned.append(
                (f"{base}/{cfg.prefix}Cert{sl.index}.lean", render_slice(cfg, arch, sl))
            )
        planned.extend(
            [
                (f"{base}/{cfg.prefix}Cert.lean", render_cert_ladder(cfg, arch)),
                (f"{base}/{cfg.prefix}CertLink.lean", render_cert_link(cfg, arch)),
                (f"{base}/{cfg.prefix}.lean", render_top_wrapper(cfg, arch)),
            ]
        )
        files.extend(planned)
    validate_generated_files(files)
    return files


def build_config(args: argparse.Namespace) -> CertConfig:
    """Resolve CLI options, preset defaults, metrics, and slices into `CertConfig`."""
    preset = resolve_preset(args.module) if args.module else None
    prefix: str | None = args.prefix or (preset.prefix if preset else None)
    if not prefix:
        raise ValueError("one of --prefix or --module is required")
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", prefix):
        raise ValueError(f"invalid --prefix identifier: {prefix}")

    stem = args.stem or (preset.stem if preset else infer_stem(prefix))
    source_mod = args.source_mod or (
        preset.source_mod if preset else infer_source_mod(prefix, stem)
    )
    proof_mod = args.proof_mod or (
        preset.proof_mod if preset else f"{source_mod}Proof"
    )
    hub_mod = preset.hub_mod if preset else None
    fns = args.fns or (preset.fns if preset and preset.fns else f"{stem}Fns")
    mod = args.mod or (preset.mod if preset and preset.mod else f"{stem}Module")
    root = Path(args.root).resolve()

    explicit_sizes: list[int] | None = None
    if args.slice_sizes:
        explicit_sizes = [int(x.strip()) for x in args.slice_sizes.split(",") if x.strip()]

    if args.target_slices is not None and args.target_slices <= 0:
        raise ValueError(f"target_slices must be positive, got {args.target_slices}")

    profile_metrics: tuple[FnMetric, ...] | None = None
    if args.profile:
        profile_metrics = load_profile_json(Path(args.profile))

    total_fns = args.total_fns
    if total_fns is None:
        if explicit_sizes is not None:
            total_fns = sum(explicit_sizes)
        else:
            detected_total = detect_total_fns(root, source_mod, fns)
            if detected_total is not None:
                total_fns = detected_total
            elif preset is not None and preset.default_total_fns is not None:
                total_fns = preset.default_total_fns
            elif profile_metrics is not None:
                total_fns = len(profile_metrics)
    if total_fns is None:
        raise ValueError(
            f"cannot infer --total-fns from {source_mod}; pass --total-fns N or --profile"
        )

    if profile_metrics is not None:
        if len(profile_metrics) != total_fns:
            raise ValueError(
                f"profile has {len(profile_metrics)} functions != total_fns {total_fns}"
            )
        fn_metrics = profile_metrics
    else:
        fn_metrics = resolve_static_metrics(root, source_mod, fns, total_fns, stem)

    uniform_slices = compute_slices(total_fns, args.slice_size, None)
    before_stats = compute_slice_stats(fn_metrics, uniform_slices, workers=args.workers)

    if explicit_sizes is not None:
        slices = compute_slices(total_fns, args.slice_size, explicit_sizes)
    elif args.balance:
        slices = autobalance_slices(
            fn_metrics,
            slice_size=args.slice_size,
            workers=args.workers,
            target_slices=args.target_slices,
            heavy_thresh=args.heavy_thresh,
        )
    else:
        slices = uniform_slices

    after_stats = compute_slice_stats(fn_metrics, slices, workers=args.workers)

    entry_idx = args.entry_idx if args.entry_idx is not None else total_fns - 1
    if not 0 <= entry_idx < total_fns:
        raise ValueError(f"--entry-idx {entry_idx} out of [0, {total_fns})")

    return CertConfig(
        prefix=prefix,
        stem=stem,
        camel_prefix=lower_camel(prefix),
        source_mod=source_mod,
        proof_mod=proof_mod,
        hub_mod=hub_mod,
        fns=fns,
        mod=mod,
        cert_name=args.cert_name or (preset.cert_name if preset and preset.cert_name else f"{stem}Cert"),
        acyclic=args.acyclic or (preset.acyclic if preset and preset.acyclic else f"{stem}_acyclic"),
        wf=args.wf or (preset.wf if preset and preset.wf else f"{fns}_wf"),
        env=args.env or (preset.env if preset and preset.env else f"{stem}Env"),
        spec_table=args.spec_table or (preset.spec_table if preset and preset.spec_table else f"{stem}SpecTable"),
        spec_sigs=args.spec_sigs or (preset.spec_sigs if preset and preset.spec_sigs else f"{stem}SpecTable_sigs"),
        module_ok=args.module_ok or (preset.module_ok if preset and preset.module_ok else f"{stem}Env_moduleOk"),
        no_exit=args.no_exit or (preset.no_exit if preset and preset.no_exit else f"{stem}Env_noExit"),
        entry_const=args.entry_const or (preset.entry_const if preset else "Full.kissat_solve_bytes"),
        entry_fn=args.entry_fn or (preset.entry_fn if preset else "kissat_solve_bytes"),
        entry_spec=args.entry_spec or (preset.entry_spec if preset else "fullSolveBytesSpec"),
        entry_idx=entry_idx,
        total_fns=total_fns,
        slices=slices,
        chunk_size=args.chunk_size,
        max_dirs=args.max_dirs,
        max_bound=args.max_bound,
        wrapper_mode=args.wrapper_mode,
        print_axioms=args.print_axioms,
        fn_metrics=fn_metrics,
        before_stats=before_stats,
        after_stats=after_stats,
    )


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    ap = argparse.ArgumentParser(
        description=(
            "Deterministic LPT cost-balanced generator for flat 1-tier "
            "LeanQbe solver cert slices."
        )
    )
    ap.add_argument(
        "--module",
        help=(
            "Solver preset name (e.g. FullM5, FullM4, FullM3, FullFast, "
            "FullFastSched, Full, Plain). Supplies canonical --prefix/--stem/paths."
        ),
    )
    ap.add_argument(
        "--prefix",
        help="Certificate module prefix (e.g. KissatM3, KissatM4, KissatM5).",
    )
    ap.add_argument(
        "--arch",
        choices=("both", "amd64", "arm64"),
        default="both",
        help="Target architectures to generate (default: both).",
    )
    ap.add_argument("--root", default=".", help="Repository root for total-fn inference.")
    ap.add_argument("--out-dir", default=".", help="Output root directory (default: .).")
    ap.add_argument("--source-mod", help="Source Kissat module (e.g. ...FullM4).")
    ap.add_argument("--proof-mod", help="Proof module (default: <source-mod>Proof).")
    ap.add_argument("--stem", help="Identifier stem (e.g. m4, m5).")
    ap.add_argument("--fns", help="Function list identifier (default: <stem>Fns).")
    ap.add_argument("--mod", help="Module identifier (default: <stem>Module).")
    ap.add_argument("--cert-name", help="Certificate def name (default: <stem>Cert).")
    ap.add_argument("--acyclic", help="Acyclic theorem name (default: <stem>_acyclic).")
    ap.add_argument("--wf", help="Well-formedness theorem name (default: <fns>_wf).")
    ap.add_argument("--env", help="Proof environment name (default: <stem>Env).")
    ap.add_argument("--spec-table", help="Spec table name (default: <stem>SpecTable).")
    ap.add_argument("--spec-sigs", help="Spec table sigs theorem name.")
    ap.add_argument("--module-ok", help="ModuleOk theorem name.")
    ap.add_argument("--no-exit", help="No-exit theorem name.")
    ap.add_argument(
        "--entry-const",
        help="Entry Fn constant for solve wrappers (default from preset or Full.kissat_solve_bytes).",
    )
    ap.add_argument(
        "--entry-fn",
        help="Entry C/QBE symbol name (default: kissat_solve_bytes).",
    )
    ap.add_argument(
        "--entry-spec",
        help="Entry Spec passed to <stem>SpecTable (default: fullSolveBytesSpec).",
    )
    ap.add_argument("--entry-idx", type=int, help="Entry index (default: total - 1).")
    ap.add_argument("--total-fns", type=int, help="Total functions in module.")
    ap.add_argument(
        "--slice-size",
        type=int,
        default=MAX_SLICE_SIZE,
        help=f"Max functions per slice, 1..{MAX_SLICE_SIZE} (default: {MAX_SLICE_SIZE}).",
    )
    ap.add_argument(
        "--slice-sizes",
        help="Comma-separated explicit slice sizes (each <= 12); disables autobalancing.",
    )
    ap.add_argument(
        "--profile",
        help="Optional JSON profile (from Lean probe) with per-fn tflatSize/loops/groups.",
    )
    ap.add_argument(
        "--balance",
        "--autobalance",
        dest="balance",
        action="store_true",
        default=True,
        help="Enable LPT cost-weighted slice autobalancing (default: enabled).",
    )
    ap.add_argument(
        "--uniform",
        "--no-balance",
        dest="balance",
        action="store_false",
        help="Disable LPT autobalancing and emit uniform --slice-size chunks.",
    )
    ap.add_argument(
        "--workers",
        type=int,
        default=DEFAULT_WORKERS,
        help=f"Parallel worker count for LPT bin packing (default: {DEFAULT_WORKERS}).",
    )
    ap.add_argument(
        "--target-slices",
        type=int,
        help="Optional target number of slices for balanced partitioning.",
    )
    ap.add_argument(
        "--heavy-thresh",
        type=float,
        help="Override function cost threshold for singleton straggler isolation.",
    )
    ap.add_argument(
        "--print-axioms",
        dest="print_axioms",
        action="store_true",
        default=True,
        help="Emit single-line <115c `#print axioms` checks in Cert/Link/Top (default: on).",
    )
    ap.add_argument(
        "--no-print-axioms",
        dest="print_axioms",
        action="store_false",
        help="Omit `#print axioms` commands from generated files.",
    )
    ap.add_argument("--chunk-size", type=int, default=4, help="Chunk size (default: 4).")
    ap.add_argument("--max-dirs", type=int, default=450, help="maxDirs (default: 450).")
    ap.add_argument(
        "--max-bound", type=int, default=2048, help="maxBound (default: 2048)."
    )
    ap.add_argument(
        "--wrapper-mode",
        choices=("full", "fnspec", "compiled"),
        default="full",
        help="Top wrapper detail level in <Prefix>.lean (default: full).",
    )
    ap.add_argument(
        "--dry-run",
        action="store_true",
        help="Validate and print plan without writing files.",
    )
    return ap.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """CLI entrypoint for `gen_cert_slices.py`."""
    args = parse_args(argv)
    try:
        cfg = build_config(args)
        arches = ["amd64", "arm64"] if args.arch == "both" else [args.arch]
        files = build_plan(cfg, arches)
    except ValueError as err:
        print(f"error: {err}", file=sys.stderr)
        return 1

    max_len = max(
        (len(line) for _, content in files for line in content.splitlines()),
        default=0,
    )
    max_loc = max((len(content.splitlines()) for _, content in files), default=0)
    slice_desc = ", ".join(
        f"S{s.index}=[{s.start},{s.end})({s.count})" for s in cfg.slices
    )
    mode = "dry-run" if args.dry_run else "write"
    metric_src = cfg.fn_metrics[0].source if cfg.fn_metrics else "none"
    bef = cfg.before_stats
    aft = cfg.after_stats
    print(
        f"gen_cert_slices ({mode}): prefix={cfg.prefix} total_fns={cfg.total_fns} "
        f"slices={len(cfg.slices)} arch={args.arch} files={len(files)} "
        f"max_line={max_len}c max_loc={max_loc} metrics={metric_src}"
    )
    print(
        f"balance BEFORE (uniform-{args.slice_size}, K={bef.num_slices}): "
        f"raw_max/mean={bef.raw_max_mean:.3f} [{bef.raw_min}..{bef.raw_max}] "
        f"cost_max/mean={bef.cost_max_mean:.3f} [{bef.cost_min:.0f}..{bef.cost_max:.0f}] "
        f"LPT{bef.lpt.workers}_makespan={bef.lpt.makespan:.0f} "
        f"(w_max/mean={bef.lpt.max_mean_ratio:.3f})"
    )
    print(
        f"balance AFTER  (K={aft.num_slices}): "
        f"raw_max/mean={aft.raw_max_mean:.3f} [{aft.raw_min}..{aft.raw_max}] "
        f"cost_max/mean={aft.cost_max_mean:.3f} [{aft.cost_min:.0f}..{aft.cost_max:.0f}] "
        f"LPT{aft.lpt.workers}_makespan={aft.lpt.makespan:.0f} "
        f"(w_max/mean={aft.lpt.max_mean_ratio:.3f})"
    )
    if aft.singletons:
        sing_str = ", ".join(f"[{idx}] {nm}({sz})" for idx, nm, sz in aft.singletons)
        print(f"isolated singletons ({len(aft.singletons)}): {sing_str}")
    print(f"slices: {slice_desc}")

    out_root = Path(args.out_dir).resolve()
    if args.dry_run:
        for rel_path, content in files:
            n_lines = len(content.splitlines())
            print(f"  [plan] {rel_path} ({n_lines} lines)")
        return 0

    for rel_path, content in files:
        dest = out_root / rel_path
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_text(content, encoding="utf-8")
        print(f"  [wrote] {dest}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
