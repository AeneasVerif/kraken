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
  - `--module FullFidelity` (aliases `KissatFidelity`, `fidelity`, `fid`):
    standalone 469-fn `KissatFidelity` solver (`FullFidelityInl`, `--max-dirs 600`,
    `--cert-style slices`, `--abi-common --hdr-model m6 --no-sound`).
  - `--module FullM8Opt` (aliases `KissatM8Opt`, `m8opt`, `opt`, `FullM8`, `m8`):
    494-fn beyond-upstream `KissatM8Opt` solver (`FullM8OptInl`, `--cert-style slices`,
    `--abi-common --hdr-model m6 --no-sound`, `--reuse-prefix KissatFidelity
    --reuse-mode pruned_relink` when `--reuse-spec` is provided).
  - `--module FullM7Fidelity`, `--module FullM7`, `--module FullM6`, `--module FullM5`,
    alongside `FullM4`, `FullM3`, `FullFast`, `FullFastSched`, `Full`, and `Plain`.
  - `--pin-cuts <json>`: splits autobalanced slices cleanly at specified cut
    boundaries (e.g. `KissatFidelity` -> `KissatM8Opt` diff boundaries).
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
DEFAULT_M6_TOTAL_FNS = 382
DEFAULT_MAX_DIRS = 450
M6_MAX_DIRS = 600
M6_NV_WORK_LEN = 6144

# Worst-case axiom report text suffix length:
#   '<ns>.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
# quotes (2) + dot (1) + " depends on axioms: [propext, Classical.choice, Quot.sound]" (59)
AXIOM_REPORT_FIXED_OVERHEAD = 62

# Known kernel-elaboration stragglers in Kissat C0 modules (including `_m5`/`_m6` suffix).
SINGLETON_STRAGGLER_RE = re.compile(
    r"^full_(?:prop_lit_raw|cong_work_step|k512_.*|bcp_.*|bva_scan_cands|"
    r"arena_sweep_m\d+)(?:_m\d+)?$"
)
HEAVY_FAMILY_RE = re.compile(
    r"^full_(?:bva_.*|viv_.*|sweep_var.*|fwd_check_cl.*|find_definition.*|"
    r"bve_var.*|factor.*|trans_lit.*|probe_prop_lit.*|substitute.*|analyze.*|"
    r"kitten_solve.*|kitten_core.*|arena_sweep.*)(?:_m\d+)?$"
)

C_TYPE_RE = (
    r"(?:static\s+|inline\s+)*(?:const\s+)?"
    r"(?:u8|u16|u32|u64|i8|i16|i32|i64|s32|s64|"
    r"uint64_t|uint32_t|int64_t|int32_t|int|void|bool|size_t)\s*\*?\s*"
)
# The lookbehind keeps a call site such as `if (!full_shrink_blk_bool_m6(h)) {` from
# being parsed as the definition of a function `_m6` returning `bool`.
C_FN_HDR_RE = re.compile(
    r"(?<![A-Za-z0-9_])" + C_TYPE_RE + r"([a-zA-Z_][a-zA-Z0-9_]*)\s*\([^;{}]*?\)\s*\{"
)
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
    init_name: str
    init_mem_entry: str
    sp_init_val: str
    ret_gpr_expr: str
    kissat_abi: str

    def unsat_reg_hyps(self, bound_expr: str, indent: str = "  ") -> list[str]:
        if self.key == "amd64":
            return [
                f"{indent}(hrdi : s.regs.get64 .rdi = cnf_ptr)",
                f"{indent}(hrsi : s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length)",
                f"{indent}(hrdx : s.regs.get64 .rdx = work_ptr)",
                f"{indent}(hrcx : s.regs.get64 .rcx = BitVec.ofNat 64 wlen)",
                f"{indent}(hr8 : s.regs.get64 .r8 = fuel)",
                f"{indent}(hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)",
                f"{indent}(hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
                f"{indent}  (region (s.regs.get64 .rsp - BitVec.ofNat 64",
                f"{indent}      {bound_expr})",
                f"{indent}    {bound_expr} ⋆",
                f"{indent}    cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem)",
            ]
        return [
            f"{indent}(hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)",
            f"{indent}(hx1 : (s.regs.getXReg .X1).toBitVec = "
            "BitVec.ofNat 64 cnfBytes.length)",
            f"{indent}(hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)",
            f"{indent}(hx3 : (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen)",
            f"{indent}(hx4 : (s.regs.getXReg .X4).toBitVec = fuel)",
            f"{indent}(hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)",
            f"{indent}(hmem : (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
            f"{indent}  region (s.regs.SP.toBitVec - BitVec.ofNat 64",
            f"{indent}      {bound_expr})",
            f"{indent}    {bound_expr} ⋆ R) s.dmem)",
        ]

    def nv_reg_preds(self, bound_expr: str) -> list[str]:
        if self.key == "amd64":
            return [
                "      s.regs.get64 .rdi = cnf_ptr ∧",
                "      s.regs.get64 .rsi = BitVec.ofNat 64 cnfBytes.length ∧",
                "      s.regs.get64 .rdx = work_ptr ∧",
                "      s.regs.get64 .rcx = BitVec.ofNat 64 wlen ∧",
                "      s.regs.get64 .r8 = fuel ∧",
                "      (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 ∧",
                "      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
                "        (region (s.regs.get64 .rsp - BitVec.ofNat 64",
                f"              {bound_expr})",
                f"            {bound_expr} ⋆",
                "          cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) s.dmem ∧",
            ]
        return [
            "      (s.regs.getXReg .X0).toBitVec = cnf_ptr ∧",
            "      (s.regs.getXReg .X1).toBitVec = BitVec.ofNat 64 cnfBytes.length ∧",
            "      (s.regs.getXReg .X2).toBitVec = work_ptr ∧",
            "      (s.regs.getXReg .X3).toBitVec = BitVec.ofNat 64 wlen ∧",
            "      (s.regs.getXReg .X4).toBitVec = fuel ∧",
            "      s.regs.X30 = ra.toUInt64 ∧",
            "      s.regs.SP.toNat % 16 = 0 ∧",
            "      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
            "        region (s.regs.SP.toBitVec - BitVec.ofNat 64",
            f"            {bound_expr})",
            f"          {bound_expr} ⋆ R) s.dmem ∧",
        ]

    def sat_nv_init_proof(
        self,
        compiled_name: str,
        cnf_bytes: str,
        work_ptr: str,
        nv_wlen: str,
        nv_pay: str,
    ) -> list[str]:
        if self.key == "amd64":
            return [
                f"  have h1 := x64InitMem_entry b 0x1234 bs ({compiled_name}.bound_le_max _)",
                f"    (by rw [{nv_pay}_length]; unfold {nv_wlen}; decide)",
                "  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ x64Target.Entry 0x0ff8#64 0x1234 b ⋆ emp at h1",
                "  dsimp only [Target.Entry, x64Target, x64FrameTarget, x64FramePreds] at h1",
                "  have h1' : (Eq (bs.At 0x1000#64) ⋆",
                "      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆",
                "        cell64 (s.regs.get64 .rsp) (0x1234 : Int64).toBitVec) ⋆ emp) s.dmem := by",
                "    rw [show s.regs.get64 .rsp = 0x0ff8#64 from rfl]; exact h1",
                f"  have hdm : (bytes nvM6CnfPtr {cnf_bytes} ⋆",
                f"      region {work_ptr} {nv_wlen} ⋆",
                "      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆",
                "        cell64 (s.regs.get64 .rsp) (0x1234 : Int64).toBitVec) ⋆ emp) s.dmem := by",
                "    refine sep_mono (Q := emp)",
                "      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))",
                f"        (fun _ heq => heq ▸ {nv_pay}_sep {cnf_bytes} (by decide))) h1'",
                "  have hhsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 := by",
                "    rw [show s.regs.get64 .rsp = 0x0ff8#64 from rfl]; decide",
            ]
        return [
            f"  have h1 := armInitMem_entry b bs ({compiled_name}.bound_le_max _)",
            f"    (by rw [{nv_pay}_length]; unfold {nv_wlen}; decide)",
            "  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 b ⋆ emp at h1",
            "  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds] at h1",
            "  simp only [region_zero, sep_emp] at h1",
            "  have h1' : (Eq (bs.At 0x1000#64) ⋆",
            "      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem := by",
            "    rw [show s.regs.SP.toBitVec = 0x1000#64 from rfl]; simpa [sep_emp] using h1",
            f"  have hdm : (bytes nvM6CnfPtr {cnf_bytes} ⋆",
            f"      region {work_ptr} {nv_wlen} ⋆",
            "      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem :=",
            "    sep_mono (Q := emp)",
            "      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))",
            f"        (fun _ heq => heq ▸ {nv_pay}_sep {cnf_bytes} (by decide))) h1'",
            "  have hhsp : s.regs.SP.toNat % 16 = 0 := by rw [show s.regs.SP = 4096 from rfl]; decide",
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
        init_name="x64Init",
        init_mem_entry="x64InitMem_entry",
        sp_init_val="0x0ff8#64",
        ret_gpr_expr="x64Target.mach.getGpr (x64Target.mach.data st) x64Init.ret0",
        kissat_abi="x64KissatAbi",
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
            "      .cons ⟨by decide, by dsimp only [get_reg]; exact hx0⟩",
            "        (.cons ⟨by decide, by dsimp only [get_reg]; exact hx1⟩",
            "          (.cons ⟨by decide, by dsimp only [get_reg]; exact hx2⟩",
            "            (.cons ⟨by decide, by dsimp only [get_reg]; exact hx3⟩",
            "              (.cons ⟨by decide, by dsimp only [get_reg]; exact hx4⟩ .nil))))⟩",
        ),
        solve_rintro_cal="hcal",
        rets_extract_lines=(
            "  have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by",
            "    exact armInit.retsIn_singleton r st.data hrets",
            "  rw [hx0']",
        ),
        solve_call_hyps="hx0 hx1 hx2 hx3 hx4 hra hsp hmem",
        unsat_solve_call_hyps="hx0 hx1 hx2 hx3 hx4 hra hsp hm_dmem'",
        unsat_rintro_cal="hcal",
        unsat_rintro_sp="hsp'",
        init_name="armInit",
        init_mem_entry="armInitMem_entry",
        sp_init_val="0x1000#64",
        ret_gpr_expr="armTarget.mach.getGpr (armTarget.mach.data st) armInit.ret0",
        kissat_abi="arm64KissatAbi",
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
    inl_mod: str | None = None
    inl_policy_mod: str | None = None
    inl_fns: str | None = None
    inl_mod_sym: str | None = None
    inl_policy: str | None = None
    sat_sound_mod: str | None = None
    sat_nv_mod: str | None = None
    hdr_model: str = "full"
    default_max_dirs: int = DEFAULT_MAX_DIRS
    emit_sound: bool = True
    source_ns: str | None = None
    proof_ns: str | None = None
    solve_spec_intro: str = "fullM6SolveBytesCoreModelSpec_intro"
    solve_spec_has_sat: bool = True
    solve_bytes_suffix: str = "_solve_bytes_iff.mpr"
    solve_mem_thm: str | None = None
    reuse_prefix: str | None = None
    reuse_inl_mod: str | None = None
    reuse_inl_fns: str | None = None
    reuse_bridge_mod: str | None = None
    reuse_thm_prefix: str | None = None
    reuse_proof_mod: str | None = None
    reuse_proof_ns: str | None = None
    reuse_acyclic: str | None = None
    reuse_wf: str | None = None
    reuse_inl_mod_sym: str | None = None
    reuse_inl_policy: str | None = None
    default_reuse_mode: str = "pruned_relink"
    default_cert_style: str = "ladder"
    default_abi_common: bool = False
    fns_length_thm: str | None = None
    default_prune_ext: bool = False
    default_no_bounds_import: bool = False
    default_tree_groups: int = 0
    default_chunk_size: int | None = None
    default_max_slice_size: int | None = None
    default_workers: int | None = None
    default_flat: bool = False


MODULE_PRESETS: dict[str, ModulePreset] = {
    "FullFidelity": ModulePreset(
        name="FullFidelity",
        prefix="KissatFidelity",
        stem="fid",
        source_mod="LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
        proof_mod="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof",
        fns="fidFns",
        mod="fidModule",
        cert_name="fidCert",
        acyclic="fid_acyclic",
        wf="fidFns_wf",
        env="fidEnv",
        spec_table="fidSpecTable",
        spec_sigs="fidSpecTable_sigs",
        module_ok="fid_moduleOk",
        no_exit="fidEnv_noExit",
        entry_const="FullM6Orch.m6oSolveBytesFn",
        entry_spec="m7FidSolveBytesSpec",
        default_total_fns=469,
        inl_mod="LeanQbe.T.Examples.Kissat.FullFidelityInlData",
        inl_policy_mod="LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy",
        inl_fns="fidInlFns",
        inl_mod_sym="fidInlMod",
        inl_policy="fidInlPolicy",
        sat_sound_mod="",
        sat_nv_mod="LeanQbe.T.Examples.Kissat.FullM6SatNv",
        hdr_model="m6",
        default_max_dirs=M6_MAX_DIRS,
        emit_sound=False,
        source_ns="LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
        proof_ns="LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
        solve_spec_intro="FullM7Fidelity.m7FidSolveBytesSpec_intro",
        solve_spec_has_sat=False,
        solve_mem_thm="fid_solveBytes_mem",
        default_cert_style="slices",
        default_abi_common=True,
        fns_length_thm="fidInlFns_length",
        default_prune_ext=True,
        default_no_bounds_import=True,
    ),
    "FullFidelityStep7": ModulePreset(
        name="FullFidelityStep7",
        prefix="KissatFidelityStep7",
        stem="fidStep7",
        source_mod="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7",
        proof_mod="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7Proof",
        fns="fidStep7Fns",
        mod="fidStep7Module",
        cert_name="fidStep7Cert",
        acyclic="fidStep7Module_acyclic",
        wf="fidStep7Module_wf",
        env="fidStep7Env",
        spec_table="fidStep7SpecTable",
        spec_sigs="fidStep7SpecTable_sigs",
        module_ok="fidStep7_moduleOk",
        no_exit="fidStep7Env_noExit",
        entry_const="FullM6Orch.m6oSolveBytesFn",
        entry_spec="m7FidSolveBytesSpec",
        default_total_fns=501,
        inl_mod="LeanQbe.T.Examples.Kissat.FullFidelityInlData",
        inl_policy_mod="LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy",
        inl_fns="fidStep7InlFns",
        inl_mod_sym="fidStep7InlMod",
        inl_policy="fidInlPolicy",
        sat_sound_mod="",
        sat_nv_mod="LeanQbe.T.Examples.Kissat.FullM6SatNv",
        hdr_model="m6",
        default_max_dirs=M6_MAX_DIRS,
        emit_sound=False,
        source_ns="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7",
        proof_ns="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep7",
        solve_spec_intro="FullM7Fidelity.m7FidSolveBytesSpec_intro",
        solve_spec_has_sat=False,
        solve_mem_thm="fidStep7_solveBytes_mem",
        default_cert_style="slices",
        default_abi_common=True,
        fns_length_thm="fidStep7InlFns_length",
        default_prune_ext=True,
        default_no_bounds_import=True,
        default_tree_groups=8,
    ),
    "FullFidelityStep11": ModulePreset(
        name="FullFidelityStep11",
        prefix="KissatFidelityStep11",
        stem="fidStep11",
        source_mod="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11",
        proof_mod="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11Proof",
        fns="fidStep11Fns",
        mod="fidStep11Module",
        cert_name="fidStep11Cert",
        acyclic="fidStep11Module_acyclic",
        wf="fidStep11Module_wf",
        env="fidStep11Env",
        spec_table="fidStep11SpecTable",
        spec_sigs="fidStep11SpecTable_sigs",
        module_ok="fidStep11_moduleOk",
        no_exit="fidStep11Env_noExit",
        entry_const="FullM6Orch.m6oSolveBytesFn",
        entry_spec="m7FidSolveBytesSpec",
        default_total_fns=505,
        inl_mod="LeanQbe.T.Examples.Kissat.FullFidelityStep11Inl",
        inl_policy_mod="LeanQbe.T.Examples.Kissat.FullFidelityInlPolicy",
        inl_fns="fidStep11InlFns",
        inl_mod_sym="fidStep11InlMod",
        inl_policy="fidInlChunkPolicy",
        sat_sound_mod="",
        sat_nv_mod="LeanQbe.T.Examples.Kissat.FullM6SatNv",
        hdr_model="m6",
        default_max_dirs=M6_MAX_DIRS,
        emit_sound=False,
        source_ns="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11",
        proof_ns="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyStep11",
        solve_spec_intro="FullM7Fidelity.m7FidSolveBytesSpec_intro",
        solve_spec_has_sat=False,
        solve_mem_thm="fidStep11_solveBytes_mem",
        default_cert_style="slices",
        default_abi_common=True,
        fns_length_thm="fidStep11InlFns_length",
        default_prune_ext=True,
        default_no_bounds_import=True,
        default_tree_groups=8,
        default_chunk_size=1,
        default_max_slice_size=500,
        default_workers=2,
        default_flat=True,
    ),
    "FullM8Opt": ModulePreset(
        name="FullM8Opt",
        prefix="KissatM8Opt",
        stem="m8Opt",
        source_mod="LeanQbe.T.Examples.Kissat.FullM8OptAssembly",
        proof_mod="LeanQbe.T.Examples.Kissat.FullM8OptAssemblyProof",
        fns="m8OptFns",
        mod="m8OptModule",
        cert_name="m8OptCert",
        acyclic="m8Opt_acyclic",
        wf="m8OptFns_wf",
        env="m8OptEnv",
        spec_table="m8OptSpecTable",
        spec_sigs="m8OptSpecTable_sigs",
        module_ok="m8Opt_moduleOk",
        no_exit="m8OptEnv_noExit",
        entry_const="FullM6Orch.m6oSolveBytesFn",
        entry_spec="m7FidSolveBytesSpec",
        default_total_fns=494,
        inl_mod="LeanQbe.T.Examples.Kissat.FullM8OptInl",
        inl_policy_mod="LeanQbe.T.Examples.Kissat.FullM8InlPolicy",
        inl_fns="m8OptInlFns",
        inl_mod_sym="m8OptInlMod",
        inl_policy="m8InlPolicy",
        sat_sound_mod="",
        sat_nv_mod="LeanQbe.T.Examples.Kissat.FullM6SatNv",
        hdr_model="m6",
        default_max_dirs=M6_MAX_DIRS,
        emit_sound=False,
        source_ns="LeanQbe.T.Examples.Kissat.FullM8OptAssembly",
        proof_ns="LeanQbe.T.Examples.Kissat.FullM8OptAssembly",
        solve_spec_intro="FullM7Fidelity.m7FidSolveBytesSpec_intro",
        solve_spec_has_sat=False,
        solve_mem_thm="m8Opt_solveBytes_mem",
        reuse_prefix="KissatFidelity",
        reuse_inl_mod="LeanQbe.T.Examples.Kissat.FullFidelityInl",
        reuse_inl_fns="fidInlFns",
        reuse_inl_mod_sym="fidInlMod",
        reuse_inl_policy="fidInlPolicy",
        reuse_proof_mod="LeanQbe.T.Examples.Kissat.FullFidelityAssemblyProof",
        reuse_proof_ns="LeanQbe.T.Examples.Kissat.FullFidelityAssembly",
        reuse_acyclic="fid_acyclic",
        reuse_wf="fidFns_wf",
        reuse_bridge_mod="LeanQbe.T.Examples.Kissat.FullFidelityM8OptBridge",
        reuse_thm_prefix="reuse_fid_eq_",
        default_reuse_mode="pruned_relink",
        default_cert_style="slices",
        default_abi_common=True,
        fns_length_thm="m8OptInlFns_length",
    ),
    "FullM7Fidelity": ModulePreset(
        name="FullM7Fidelity",
        prefix="KissatM7Fidelity",
        stem="m7Fidelity",
        source_mod="LeanQbe.T.Examples.Kissat.FullM7FidelityAssembly",
        proof_mod="LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof",
        hub_mod="LeanQbe.T.Examples.Kissat.M5Hub",
        module_ok="m7Fidelity_moduleOk",
        no_exit="m7FidelityEnv_noExit",
        entry_const="FullM6Orch.m6oSolveBytesFn",
        entry_spec="m7FidSolveBytesSpec",
        default_total_fns=413,
        inl_mod="LeanQbe.T.Examples.Kissat.FullM7FidelityInl",
        inl_policy_mod="LeanQbe.T.Examples.Kissat.FullM7InlPolicy",
        inl_fns="m7FidInlFns",
        inl_mod_sym="m7FidInlMod",
        inl_policy="m7InlPolicy",
        sat_sound_mod="",
        sat_nv_mod="LeanQbe.T.Examples.Kissat.FullM6SatNv",
        hdr_model="m6",
        default_max_dirs=M6_MAX_DIRS,
        emit_sound=False,
        source_ns="LeanQbe.T.Examples.Kissat.FullM7Fidelity",
        proof_ns="LeanQbe.T.Examples.Kissat.FullM7Fidelity",
        solve_spec_intro="m7FidSolveBytesSpec_intro",
        solve_spec_has_sat=False,
        solve_mem_thm="m7Fidelity_solveBytes_mem",
        reuse_prefix="KissatM7Plus",
        reuse_inl_mod="LeanQbe.T.Examples.Kissat.FullM7PlusInl",
        reuse_inl_fns="m7PlusInlFns",
        reuse_inl_mod_sym="m7PlusInlMod",
        reuse_inl_policy="m7InlPolicy",
        reuse_proof_mod="LeanQbe.T.Examples.Kissat.FullM7PlusAssembly",
        reuse_proof_ns="LeanQbe.T.Examples.Kissat.FullM7Plus",
        reuse_acyclic="m7Plus_acyclic",
        reuse_wf="m7PlusFns_wf",
    ),
    "FullM7Plus": ModulePreset(
        name="FullM7Plus",
        prefix="KissatM7Plus",
        stem="m7Plus",
        source_mod="LeanQbe.T.Examples.Kissat.FullM7PlusAssembly",
        proof_mod="LeanQbe.T.Examples.Kissat.FullM7PlusAssemblyProof",
        hub_mod="LeanQbe.T.Examples.Kissat.M5Hub",
        module_ok="m7Plus_moduleOk",
        entry_const="FullM6Orch.m6oSolveBytesFn",
        entry_spec="m7PlusSolveBytesSpec",
        default_total_fns=410,
        inl_mod="LeanQbe.T.Examples.Kissat.FullM7PlusInl",
        inl_policy_mod="LeanQbe.T.Examples.Kissat.FullM7InlPolicy",
        inl_fns="m7PlusInlFns",
        inl_mod_sym="m7PlusInlMod",
        inl_policy="m7InlPolicy",
        sat_sound_mod="",
        sat_nv_mod="LeanQbe.T.Examples.Kissat.FullM6SatNv",
        hdr_model="m6",
        default_max_dirs=M6_MAX_DIRS,
        emit_sound=False,
        source_ns="LeanQbe.T.Examples.Kissat.FullM7Plus",
        proof_ns="LeanQbe.T.Examples.Kissat.FullM7Plus",
        solve_spec_intro="m7PlusSolveBytesSpec_intro",
        solve_spec_has_sat=False,
        solve_bytes_suffix="_solve_bytes",
        solve_mem_thm="m7Plus_solveBytes_mem",
    ),
    "FullM7": ModulePreset(
        name="FullM7",
        prefix="KissatM7",
        stem="m7",
        source_mod="LeanQbe.T.Examples.Kissat.FullM7",
        proof_mod="LeanQbe.T.Examples.Kissat.FullM7Proof",
        hub_mod="LeanQbe.T.Examples.Kissat.M5Hub",
        entry_const="FullM6Orch.m6oSolveBytesFn",
        entry_spec="fullM6SolveBytesCoreModelSpec",
        default_total_fns=None,
        inl_mod="LeanQbe.T.Examples.Kissat.FullM7Inl",
        inl_policy_mod="LeanQbe.T.Examples.Kissat.FullM7InlPolicy",
        inl_fns="m7InlFns",
        inl_mod_sym="m7InlMod",
        inl_policy="m7InlPolicy",
        sat_sound_mod="LeanQbe.T.Examples.Kissat.FullM6SatSound",
        sat_nv_mod="LeanQbe.T.Examples.Kissat.FullM6SatNv",
        hdr_model="m6",
        default_max_dirs=M6_MAX_DIRS,
    ),
    "FullM6": ModulePreset(
        name="FullM6",
        prefix="KissatM6",
        stem="m6",
        source_mod="LeanQbe.T.Examples.Kissat.FullM6",
        proof_mod="LeanQbe.T.Examples.Kissat.FullM6Proof",
        hub_mod="LeanQbe.T.Examples.Kissat.M5Hub",
        env="m6CoreEnv",
        module_ok="m6CoreEnv_moduleOk",
        no_exit="m6CoreEnv_noExit",
        entry_const="FullM6Orch.m6oSolveBytesFn",
        entry_spec="fullM6SolveBytesCoreModelSpec",
        default_total_fns=DEFAULT_M6_TOTAL_FNS,
        inl_mod="LeanQbe.T.Examples.Kissat.FullM6Inl",
        inl_policy_mod="LeanQbe.T.Examples.Kissat.FullM6InlPolicy",
        inl_fns="m6InlFns",
        inl_mod_sym="m6InlMod",
        inl_policy="m6InlPolicy",
        hdr_model="m6",
        default_max_dirs=M6_MAX_DIRS,
        emit_sound=False,
    ),
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
    "kissatfidelity": "FullFidelity",
    "fidelity": "FullFidelity",
    "fid": "FullFidelity",
    "kissatfidelitystep7": "FullFidelityStep7",
    "fidelitystep7": "FullFidelityStep7",
    "fidstep7": "FullFidelityStep7",
    "step7": "FullFidelityStep7",
    "kissatfidelitystep11": "FullFidelityStep11",
    "fidelitystep11": "FullFidelityStep11",
    "fidstep11": "FullFidelityStep11",
    "step11": "FullFidelityStep11",
    "kissatm8opt": "FullM8Opt",
    "m8opt": "FullM8Opt",
    "opt": "FullM8Opt",
    "fullm8": "FullM8Opt",
    "m8": "FullM8Opt",
    "kissatplain": "Plain",
    "m7fidelity": "FullM7Fidelity",
    "m7_fidelity": "FullM7Fidelity",
    "m7fid": "FullM7Fidelity",
    "m7plus": "FullM7Plus",
    "m7_plus": "FullM7Plus",
    "m7": "FullM7",
    "m6": "FullM6",
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
    reuse_src_index: int | None = None
    src_start: int | None = None

    @property
    def end(self) -> int:
        return self.start + self.count

    @property
    def reuse_src_start(self) -> int:
        """Starting index in the reuse source module's `fns` list."""
        return self.src_start if self.src_start is not None else self.start


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
    work: int = 0


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
    inl_mod: str | None = None
    inl_policy_mod: str | None = None
    inl_fns: str | None = None
    inl_mod_sym: str | None = None
    inl_policy: str | None = None
    sat_sound_mod: str | None = None
    sat_nv_mod: str | None = None
    hdr_model: str = "full"
    emit_sound: bool = True
    unsat_env: str = ""
    unsat_module_ok: str = ""
    unsat_no_exit: str = ""
    sound_env: str = ""
    sound_module_ok: str = ""
    sound_no_exit: str = ""
    source_ns: str = ""
    proof_ns: str = ""
    solve_spec_intro: str = "fullM6SolveBytesCoreModelSpec_intro"
    solve_spec_has_sat: bool = True
    solve_bytes_suffix: str = "_solve_bytes_iff.mpr"
    solve_mem_thm: str | None = None
    reuse_prefix: str | None = None
    reuse_inl_mod: str | None = None
    reuse_inl_fns: str | None = None
    reuse_bridge_mod: str | None = None
    reuse_thm_prefix: str | None = None
    reuse_mode: str = "verbatim"
    reuse_proof_mod: str | None = None
    reuse_proof_ns: str | None = None
    reuse_acyclic: str | None = None
    reuse_wf: str | None = None
    reuse_inl_mod_sym: str | None = None
    reuse_inl_policy: str | None = None
    cert_style: str = "ladder"
    abi_common: bool = False
    fns_length_thm: str | None = None
    prune_ext: bool = False
    no_bounds_import: bool = False
    bounds_literals: (
        dict[str, dict[int, tuple[tuple[str, tuple[str, ...], tuple[str, ...], int], ...]]] | None
    ) = None
    tree_groups: int = 0
    max_slice_weight: float | None = None
    flat: bool = False

    @property
    def is_inlined(self) -> bool:
        """Whether slices compile an external chunked/materialized `inl_mod`."""
        return bool(self.inl_mod)

    @property
    def open_source_ns(self) -> str:
        """Namespace exported by `source_mod` (defaults to `source_mod`)."""
        return self.source_ns or self.source_mod

    @property
    def open_proof_ns(self) -> str:
        """Namespace exported by `proof_mod` (defaults to `proof_mod`)."""
        return self.proof_ns or self.proof_mod

    @property
    def cert_fns(self) -> str:
        """Function list identifier compiled by `Bounds` and `Cert1..N`."""
        return self.inl_fns if self.is_inlined and self.inl_fns else self.fns

    @property
    def cert_source_mod(self) -> str:
        """Module defining `cert_fns` for `Bounds` and `Cert1..N`."""
        return self.inl_mod if self.is_inlined and self.inl_mod else self.source_mod

    @property
    def cert_source_ns(self) -> str:
        """Namespace for `cert_source_mod`."""
        return self.inl_mod if self.is_inlined and self.inl_mod else self.open_source_ns

    @property
    def target_mod_expr(self) -> str:
        """Module type expression proved by `<Prefix>Cert.<cert_name>`."""
        if self.is_inlined and self.inl_policy:
            return f"{self.mod}.optInlinePolicy {self.inl_policy}"
        return self.mod

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


def _split_top_level_ws(expr: str) -> list[str]:
    """Split `expr` on whitespace outside parentheses/brackets/angle-brackets."""
    parts: list[str] = []
    depth = 0
    cur: list[str] = []
    for ch in expr:
        if ch in "([⟨":
            depth += 1
            cur.append(ch)
        elif ch in ")]⟩":
            depth = max(0, depth - 1)
            cur.append(ch)
        elif depth == 0 and ch.isspace():
            if cur:
                parts.append("".join(cur))
                cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur))
    return parts


def _scan_kissat_sources(
    kissat_dir: Path,
) -> tuple[
    dict[str, dict[str, int | str]],
    dict[str, list[tuple[str, str]]],
    dict[str, str],
    dict[str, tuple[str, str]],
    dict[str, str],
]:
    """Collect C0 body metrics, `<pfx>_fns` literals, `List Fn`/`befores` defs, and `Fn` aliases."""
    c_metrics: dict[str, dict[str, int | str]] = {}
    list_literals: dict[str, list[tuple[str, str]]] = {}
    list_exprs: dict[str, str] = {}
    fn_aliases: dict[str, tuple[str, str]] = {}
    before_exprs: dict[str, str] = {}

    if not kissat_dir.is_dir():
        return c_metrics, list_literals, list_exprs, fn_aliases, before_exprs

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
        body_aliases: dict[str, str] = {}
        for bm in re.finditer(
            r"(?:def|private\s+def|abbrev)\s+(\w+)(?:\s*:\s*Func\b.*?)?\s*:=\s*(.*?)"
            r"(?=\n(?:def|private|theorem|abbrev|end|@|/-))",
            clean,
            re.S,
        ):
            m_bdy = re.search(
                r"\b((?:full|kissat|plain|m6|m8)_[a-zA-Z0-9_]+?)_body\b", bm.group(2)
            )
            if m_bdy:
                body_aliases[bm.group(1)] = m_bdy.group(1)

        for dm in re.finditer(
            r"(?:def|private\s+def|abbrev)\s+(\w+)\s*:\s*Fn\s*:=\s*(.*?)"
            r"(?=\n(?:def|private|theorem|abbrev|end|@|/-))",
            clean,
            re.S,
        ):
            lhs, rhs = dm.group(1), dm.group(2)
            m_nm = re.search(r'"([a-zA-Z0-9_]+)"', rhs)
            m_bdy = re.search(r"\b((?:full|kissat|plain|m6|m8)_[a-zA-Z0-9_]+?)_body\b", rhs)
            src_nm = m_bdy.group(1) if m_bdy else None
            if src_nm is None:
                for tok in re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", rhs):
                    if tok in body_aliases:
                        src_nm = body_aliases[tok]
                        break
            if src_nm is None:
                src_nm = m_nm.group(1) if m_nm else lhs
            out_nm = m_nm.group(1) if m_nm else src_nm
            fn_aliases[lhs] = (out_nm, src_nm)
            fn_aliases[f"{mod_short}.{lhs}"] = (out_nm, src_nm)

        for lm in re.finditer(
            r"(?:def|private\s+def|abbrev)\s+(\w+)\s*:\s*List\s+Fn\s*:=\s*(.*?)"
            r"(?=\n(?:def|private|theorem|abbrev|end|@|/\-))",
            clean,
            re.S,
        ):
            lhs, rhs = lm.group(1), lm.group(2)
            list_exprs.setdefault(lhs, rhs)
            list_exprs[f"{mod_short}.{lhs}"] = rhs

        for bef in re.finditer(
            r"(?:def|private\s+def|abbrev)\s+(\w+)\s*:\s*List\s*\(\s*Sym\s*×\s*List\s+Fn\s*\)\s*:=\s*(.*?)"
            r"(?=\n(?:def|private|theorem|abbrev|end|@|/\-))",
            clean,
            re.S,
        ):
            lhs, rhs = bef.group(1), bef.group(2)
            before_exprs.setdefault(lhs, rhs)
            before_exprs[f"{mod_short}.{lhs}"] = rhs

    return c_metrics, list_literals, list_exprs, fn_aliases, before_exprs


def _eval_fn_lists(
    target_key: str,
    list_literals: dict[str, list[tuple[str, str]]],
    list_exprs: dict[str, str],
    fn_aliases: dict[str, tuple[str, str]],
    before_exprs: dict[str, str] | None = None,
) -> list[tuple[str, str]]:
    """Statically evaluate `++`, `.take`, `.drop`, `[..]`, `spliceFns`, `patchFns`."""
    memo: dict[str, list[tuple[str, str]]] = {}
    bef_map_src = before_exprs or {}

    def eval_fn_item(item: str) -> tuple[str, str]:
        s = item.strip()
        m_lit = re.match(r'^⟨"([^"]+)"\s*,.*?,\s*([A-Za-z0-9_.]+)_body\s*⟩$', s, re.S)
        if m_lit:
            return (m_lit.group(1), m_lit.group(2).split(".")[-1])
        m_rec = re.match(
            r'^\{\s*name\s*:=\s*"([^"]+)"[^{}]*?\bbody\s*:=\s*([A-Za-z0-9_.]+)_body\s*\}$',
            s,
            re.S,
        )
        if m_rec:
            return (m_rec.group(1), m_rec.group(2).split(".")[-1])
        if s in fn_aliases:
            return fn_aliases[s]
        short = s.split(".")[-1]
        return fn_aliases.get(short, (short, short))

    def eval_befores(expr: str, seen: set[str]) -> list[tuple[str, list[tuple[str, str]]]]:
        p = _unwrap_parens(expr)
        if "++" in p:
            parts = _split_top_level(p, "++")
            if len(parts) > 1:
                out_b: list[tuple[str, list[tuple[str, str]]]] = []
                for part in parts:
                    out_b.extend(eval_befores(part, seen))
                return out_b
        if p.startswith("[") and p.endswith("]"):
            inner = p[1:-1].strip()
            if not inner:
                return []
            out_b = []
            for it in _split_top_level(inner, ","):
                tup = _unwrap_parens(it)
                pair = _split_top_level(tup, ",")
                if len(pair) == 2:
                    m_anc = re.search(r'"([^"]+)"', pair[0])
                    if m_anc:
                        out_b.append((m_anc.group(1), eval_expr(pair[1], seen)))
            return out_b
        short = p.split(".")[-1]
        resolved = p if p in bef_map_src else (short if short in bef_map_src else "")
        if not resolved or resolved in seen:
            return []
        return eval_befores(bef_map_src[resolved], seen | {resolved})

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
        if "++" in p:
            parts = _split_top_level(p, "++")
            if len(parts) > 1:
                out_app: list[tuple[str, str]] = []
                for part in parts:
                    out_app.extend(eval_expr(part, seen))
                return out_app
        if p.startswith("[") and p.endswith("]"):
            inner = p[1:-1].strip()
            if not inner:
                return []
            return [eval_fn_item(it) for it in _split_top_level(inner, ",") if it.strip()]
        m_patch = re.match(r"^(?:mfPatchFns|fidPatchFns|patchFns)\s+(.+)$", p, re.S)
        if m_patch:
            args = _split_top_level_ws(m_patch.group(1))
            if len(args) == 3:
                rep_pairs = eval_expr(args[0], seen)
                bef_list = eval_befores(args[1], seen)
                fs_pairs = eval_expr(args[2], seen)
                rep_map = {out_nm: (out_nm, src_nm) for out_nm, src_nm in rep_pairs}
                bef_by_anchor: dict[str, list[tuple[str, str]]] = {}
                for anc, hs in bef_list:
                    bef_by_anchor.setdefault(anc, []).extend(hs)
                out_p: list[tuple[str, str]] = []
                for out_nm, src_nm in fs_pairs:
                    if out_nm in bef_by_anchor:
                        out_p.extend(bef_by_anchor[out_nm])
                    out_p.append(rep_map.get(out_nm, (out_nm, src_nm)))
                return out_p
        m_splice = re.match(r"^(?:mpSpliceFns|spliceFns)\s+(.+)$", p, re.S)
        if m_splice:
            args = _split_top_level_ws(m_splice.group(1))
            if len(args) == 2:
                rep_pairs = eval_expr(args[0], seen)
                fs_pairs = eval_expr(args[1], seen)
                rep_map = {out_nm: (out_nm, src_nm) for out_nm, src_nm in rep_pairs}
                return [rep_map.get(out_nm, (out_nm, src_nm)) for out_nm, src_nm in fs_pairs]
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
    c_metrics, list_literals, list_exprs, fn_aliases, before_exprs = _scan_kissat_sources(
        kissat_dir
    )
    src_short = source_mod.split(".")[-1]
    fn_pairs = _eval_fn_lists(
        f"{src_short}.{fns_sym}", list_literals, list_exprs, fn_aliases, before_exprs
    )

    if not fn_pairs and stem == "m5":
        m4_pairs = _eval_fn_lists(
            "FullM4.m4Fns", list_literals, list_exprs, fn_aliases, before_exprs
        )
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
                "ir_size",
                row.get(
                    "mid_tflat_size",
                    row.get(
                        "tflat_size",
                        row.get("inl_tflat_size", row.get("raw_size", row.get("size", 80))),
                    ),
                ),
            )
        )
        loops = int(row.get("mid_loops", row.get("loops", row.get("raw_loops", 0))))
        groups = int(row.get("mid_groups", row.get("groups", row.get("raw_groups", 1))))
        calls = int(row.get("mid_calls", row.get("calls", row.get("raw_calls", 0))))
        work = int(
            row.get("work", int(row.get("jnz", 0)) + int(row.get("defer", 0)))
        )
        explicit = row.get("cost", row.get("weight"))
        if explicit is not None:
            cost = float(explicit)
        elif work > 0:
            cost = max(1.0, 68.38 * size + 2.355 * work)
        else:
            cost = compute_fn_cost(size, loops, groups, calls)
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
                work=work,
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


def load_pin_cuts(path: Path, total_fns: int) -> tuple[int, ...]:
    """Load function-index cut boundaries from JSON (`list[int]`, `{cuts}`, or `{runs}`)."""
    raw = json.loads(path.read_text(encoding="utf-8"))
    cuts: set[int] = set()
    if isinstance(raw, list):
        cuts.update(int(x) for x in raw)
    elif isinstance(raw, dict):
        if "cuts" in raw or "pin_cuts" in raw:
            seq = raw.get("cuts", raw.get("pin_cuts", []))
            cuts.update(int(x) for x in seq)
        if "runs" in raw:
            for item in raw["runs"]:
                if isinstance(item, dict):
                    st = int(item["start"])
                    en = int(item["end"]) if "end" in item else st + int(item["count"])
                    cuts.update((st, en))
                elif isinstance(item, (list, tuple)) and len(item) >= 2:
                    cuts.update((int(item[0]), int(item[1])))
    else:
        raise ValueError(f"unsupported --pin-cuts JSON format in {path}")
    return tuple(sorted(c for c in cuts if 0 < c < total_fns))


def apply_pin_cuts(
    ranges: list[tuple[int, int]],
    pin_cuts: tuple[int, ...] | list[int] | None,
) -> list[tuple[int, int]]:
    """Split any `(start, end)` slice straddling a boundary in `pin_cuts`."""
    if not pin_cuts:
        return ranges
    cuts = sorted(set(int(c) for c in pin_cuts))
    out: list[tuple[int, int]] = []
    for s, e in ranges:
        cur = s
        for c in cuts:
            if cur < c < e:
                out.append((cur, c))
                cur = c
        out.append((cur, e))
    return out


def autobalance_slices(
    metrics: tuple[FnMetric, ...],
    slice_size: int = MAX_SLICE_SIZE,
    workers: int = DEFAULT_WORKERS,
    target_slices: int | None = None,
    heavy_thresh: float | None = None,
    file_overhead: float = DEFAULT_FILE_OVERHEAD,
    pin_cuts: tuple[int, ...] | list[int] | None = None,
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

    chosen = apply_pin_cuts(chosen, pin_cuts)
    return tuple(
        SliceRange(index=idx, start=s, count=e - s)
        for idx, (s, e) in enumerate(chosen, start=1)
    )


def singleton_isolated_slices(
    metrics: tuple[FnMetric, ...],
    singleton_size: int = 350,
    singleton_work: int = 2100,
    max_slice_size: int = 500,
    max_slice_count: int = 10,
    max_slice_weight: float | None = None,
    singleton_weight: float | None = None,
) -> tuple[SliceRange, ...]:
    """Isolate heavy functions (`size >= singleton_size`, `work >= singleton_work`, or
    `cost >= singleton_weight`) as singletons and pack remaining functions under
    `max_slice_size`, `max_slice_weight`, and `max_slice_count`."""
    if not metrics:
        raise ValueError("cannot slice 0 functions")
    if not 1 <= max_slice_count <= MAX_SLICE_SIZE:
        raise ValueError(
            f"max_slice_count must be in [1, {MAX_SLICE_SIZE}], got {max_slice_count}"
        )
    if max_slice_size < 0 or (max_slice_size == 0 and max_slice_weight is None):
        raise ValueError(f"max_slice_size must be positive, got {max_slice_size}")
    if max_slice_weight is not None and max_slice_weight <= 0:
        raise ValueError(f"max_slice_weight must be positive, got {max_slice_weight}")
    eff_sing_wt = (
        singleton_weight
        if singleton_weight is not None
        else (0.65 * max_slice_weight if max_slice_weight is not None else None)
    )
    ranges: list[tuple[int, int]] = []
    cur_start: int | None = None
    cur_cnt = 0
    cur_sz = 0
    cur_wt = 0.0
    for idx, m in enumerate(metrics):
        is_heavy = (
            (singleton_size > 0 and m.size >= singleton_size)
            or (singleton_work > 0 and m.work >= singleton_work)
            or (eff_sing_wt is not None and eff_sing_wt > 0 and m.cost >= eff_sing_wt)
            or (max_slice_weight is not None and bool(SINGLETON_STRAGGLER_RE.match(m.name)))
        )
        if is_heavy:
            if cur_start is not None:
                ranges.append((cur_start, idx))
                cur_start = None
                cur_cnt = 0
                cur_sz = 0
                cur_wt = 0.0
            ranges.append((idx, idx + 1))
        else:
            exceeds_size = max_slice_size > 0 and (cur_sz + m.size > max_slice_size)
            exceeds_wt = max_slice_weight is not None and (cur_wt + m.cost > max_slice_weight)
            if cur_start is not None and (
                cur_cnt >= max_slice_count or exceeds_size or exceeds_wt
            ):
                ranges.append((cur_start, idx))
                cur_start = idx
                cur_cnt = 1
                cur_sz = m.size
                cur_wt = m.cost
            else:
                if cur_start is None:
                    cur_start = idx
                cur_cnt += 1
                cur_sz += m.size
                cur_wt += m.cost
    if cur_start is not None:
        ranges.append((cur_start, len(metrics)))
    return tuple(
        SliceRange(index=i, start=s, count=e - s)
        for i, (s, e) in enumerate(ranges, start=1)
    )


def plan_slices_with_reuse(
    metrics: tuple[FnMetric, ...],
    reuse_entries: list[dict[str, int]],
    slice_size: int,
    workers: int,
    balance: bool,
    singleton_size: int | None,
    singleton_work: int | None,
    max_slice_size: int | None,
    heavy_thresh: float | None,
    fresh_sizes: list[int] | None = None,
    max_slice_weight: float | None = None,
    singleton_weight: float | None = None,
) -> tuple[SliceRange, ...]:
    """Partition `[0, len(metrics))` keeping reused slices and slicing uncovered gaps."""
    total_fns = len(metrics)
    reused = sorted(
        [
            (
                int(r["start"]),
                int(r["count"]),
                int(r["src_index"]),
                int(r["src_start"]) if "src_start" in r and r["src_start"] is not None else None,
            )
            for r in reuse_entries
        ],
        key=lambda x: x[0],
    )
    prev_end = 0
    for st, cnt, src_idx, _ in reused:
        if cnt <= 0 or st < 0 or st + cnt > total_fns:
            raise ValueError(f"invalid reused slice src={src_idx} [{st}, {st + cnt})")
        if st < prev_end:
            raise ValueError(f"overlapping reused slice at start={st} < prev_end={prev_end}")
        prev_end = st + cnt

    combined: list[SliceRange] = []
    fresh_idx = 0
    fresh_iter = iter(fresh_sizes) if fresh_sizes is not None else None

    def slice_gap(g_start: int, g_end: int) -> None:
        nonlocal fresh_idx
        if g_start >= g_end:
            return
        if fresh_iter is not None:
            cur = g_start
            while cur < g_end:
                try:
                    cnt = next(fresh_iter)
                except StopIteration as exc:
                    raise ValueError(
                        f"fresh_sizes exhausted cleanly before gap [{g_start}, {g_end})"
                    ) from exc
                if cnt <= 0 or cnt > slice_size or cur + cnt > g_end:
                    raise ValueError(
                        f"invalid fresh slice size {cnt} for gap [{cur}, {g_end})"
                    )
                fresh_idx += 1
                combined.append(SliceRange(index=fresh_idx, start=cur, count=cnt))
                cur += cnt
            return
        sub = metrics[g_start:g_end]
        if (
            max_slice_size is not None
            or singleton_size is not None
            or max_slice_weight is not None
        ):
            if max_slice_weight is not None and max_slice_size is None and singleton_size is None:
                s_sz = 0
                s_wk = singleton_work if singleton_work is not None else 0
                m_sz = 0
            else:
                s_sz = singleton_size if singleton_size is not None else 350
                s_wk = singleton_work if singleton_work is not None else s_sz * 6
                m_sz = max_slice_size if max_slice_size is not None else 500
            gap_slices = singleton_isolated_slices(
                sub,
                singleton_size=s_sz,
                singleton_work=s_wk,
                max_slice_size=m_sz,
                max_slice_count=slice_size,
                max_slice_weight=max_slice_weight,
                singleton_weight=singleton_weight,
            )
        elif balance:
            gap_slices = autobalance_slices(
                sub, slice_size=slice_size, workers=workers, heavy_thresh=heavy_thresh
            )
        else:
            gap_slices = compute_slices(len(sub), slice_size, None)
        for gs in gap_slices:
            fresh_idx += 1
            combined.append(
                SliceRange(index=fresh_idx, start=g_start + gs.start, count=gs.count)
            )

    pos = 0
    for st, cnt, src_idx, s_start in reused:
        slice_gap(pos, st)
        combined.append(
            SliceRange(
                index=src_idx,
                start=st,
                count=cnt,
                reuse_src_index=src_idx,
                src_start=s_start,
            )
        )
        pos = st + cnt
    slice_gap(pos, total_fns)
    if fresh_iter is not None:
        leftover = list(fresh_iter)
        if leftover:
            raise ValueError(f"unused trailing fresh_sizes: {leftover}")

    assert combined and combined[0].start == 0 and combined[-1].end == total_fns
    for a, b in zip(combined, combined[1:]):
        assert a.end == b.start
    return tuple(combined)


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


def is_materialized_inl_mod(mod: str) -> bool:
    """True for `inline_mod*`-materialized (`noncomputable` `TFlatFn`) `.olean` modules."""
    return bool(mod) and ("Inl" in mod) and not mod.endswith("Data") and not mod.endswith(
        "FullFidelityInl"
    )


def render_bounds(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>Bounds.lean` using `eval_prefix_ext!`."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}Bounds"
    mb_opt = fmt_max_bound_opt(cfg.max_bound)
    flat_opt = " (flat := true)" if cfg.flat else ""
    cert_fns = cfg.cert_fns
    cert_src = cfg.cert_source_mod
    eval_call = (
        f"eval_prefix_ext! {cfg.stem}AllExt {arch.targ} {arch.lt} "
        f"{cert_fns}{mb_opt}\n"
        f"  (prefixDef := {cfg.stem}ExtPrefix){flat_opt}"
    )
    if any(len(ln) > MAX_LINE_LEN for ln in eval_call.splitlines()):
        eval_call = (
            f"eval_prefix_ext! {cfg.stem}AllExt\n"
            f"  {arch.targ} {arch.lt} {cert_fns}{mb_opt}\n"
            f"  (prefixDef := {cfg.stem}ExtPrefix){flat_opt}"
        )

    hub_note = f" (hub `{cfg.hub_mod}`)" if cfg.hub_mod else ""
    lines = [
        "module",
        "",
        "public import LeanQbe.T.Main",
        *(["public import LeanQbe.T.MainCertFlat"] if cfg.flat else []),
        f"public import {arch.targ_mod}",
        f"public import {cert_src}",
        "meta import Lean",
        "meta import LeanQbe.T.MainCertElab",
        *(["meta import LeanQbe.T.MainCertFlatElab"] if cfg.flat else []),
        f"meta import {arch.targ_mod}",
        *([] if is_materialized_inl_mod(cert_src) else [f"meta import {cert_src}"]),
        "",
        "/-!",
        f"# {cfg.prefix} Auto-Computed Prefix Bounds on {arch.isa_title}",
        "",
        *wrap_comment_lines(
            f"Precomputes `(SigEntry × Nat)` stack bounds across all "
            f"`{cfg.total_fns}` functions of `{cert_src}.{cert_fns}`"
            f"{hub_note} via `eval_prefix_ext!`, enabling flat 1-tier parallel "
            "slice certificates via `<prefix>ExtPrefix`."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(["LeanQbe.T", arch.ns_prefix, cfg.cert_source_ns]),
        "",
        "-- Auto-computed reversed `(sig, bound)` accumulator and prefix slicer for the module.",
        eval_call,
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def _format_lean_ty(ty: str) -> str:
    """Format a Lean `Ty` literal concisely (`i64`, `i32`, `.bool`, etc.)."""
    s = ty.strip()
    aliases = {
        "i64": "i64",
        "u64": "i64",
        "i32": "i32",
        "u32": "i32",
        "i16": "i16",
        "u16": "i16",
        "i8": "i8",
        "u8": "i8",
        "bool": ".bool",
        "f32": ".f32",
        "f64": ".f64",
    }
    return aliases.get(s, s)


def _parse_bound_entry(raw: dict[str, object]) -> tuple[str, tuple[str, ...], tuple[str, ...], int]:
    """Parse one `{name, as, rs, bound}` JSON record into a normalized tuple."""
    name = str(raw["name"])
    as_tys = tuple(_format_lean_ty(str(t)) for t in raw.get("as", []))  # type: ignore[union-attr]
    rs_tys = tuple(_format_lean_ty(str(t)) for t in raw.get("rs", []))  # type: ignore[union-attr]
    bound = int(raw["bound"])  # type: ignore[arg-type]
    return (name, as_tys, rs_tys, bound)


def load_bounds_json(
    path: Path,
    slices: tuple[SliceRange, ...],
    total_fns: int,
) -> dict[str, dict[int, tuple[tuple[str, tuple[str, ...], tuple[str, ...], int], ...]]]:
    """Load per-slice literal callee bounds (`N2`) from JSON for `amd64`/`arm64`.

    Accepts:
      1. `{"amd64": {"2": [entry, ...], ...}, "arm64": {...}}` (per-arch per-slice map)
      2. `{"slices": {"2": [entry, ...], ...}}` (arch-agnostic per-slice map)
      3. `{"amd64": [fn_row, ...], "arm64": [...]}` or `[fn_row, ...]` (per-fn module-order
         list; if `fn_row` carries `"callees"`, prunes each slice to its direct prefix callees).
    """
    raw = json.loads(path.read_text(encoding="utf-8"))

    def resolve_for_payload(
        payload: object,
    ) -> dict[int, tuple[tuple[str, tuple[str, ...], tuple[str, ...], int], ...]]:
        if isinstance(payload, dict):
            table = payload.get("slices", payload)
            if not isinstance(table, dict):
                raise ValueError(f"invalid bounds JSON slice map in {path}")
            out: dict[int, tuple[tuple[str, tuple[str, ...], tuple[str, ...], int], ...]] = {}
            for k, entries in table.items():
                if not isinstance(entries, list):
                    raise ValueError(f"bounds JSON slice {k!r} must be a list")
                out[int(k)] = tuple(_parse_bound_entry(e) for e in entries)
            return out
        if isinstance(payload, list):
            if len(payload) != total_fns:
                raise ValueError(
                    f"bounds JSON has {len(payload)} function rows != total_fns {total_fns}"
                )
            parsed = [_parse_bound_entry(e) for e in payload]
            callees_list = [
                list(e["callees"]) if isinstance(e, dict) and "callees" in e else None
                for e in payload
            ]
            has_callees = any(c is not None for c in callees_list)
            out = {}
            for sl in slices:
                if sl.start == 0:
                    out[sl.index] = ()
                    continue
                prefix = parsed[: sl.start]
                if has_callees:
                    by_name = {entry[0]: entry for entry in prefix}
                    seen: set[str] = set()
                    pruned: list[tuple[str, tuple[str, ...], tuple[str, ...], int]] = []
                    for idx in range(sl.start, sl.end):
                        for callee in callees_list[idx] or ():
                            nm = str(callee)
                            if nm in by_name and nm not in seen:
                                seen.add(nm)
                                pruned.append(by_name[nm])
                    out[sl.index] = tuple(pruned)
                else:
                    out[sl.index] = tuple(reversed(prefix))
            return out
        raise ValueError(f"unsupported bounds JSON structure in {path}")

    if isinstance(raw, dict) and ("amd64" in raw or "arm64" in raw):
        return {
            arch_k: resolve_for_payload(raw[arch_k])
            for arch_k in ("amd64", "arm64")
            if arch_k in raw
        }
    shared = resolve_for_payload(raw)
    return {"amd64": shared, "arm64": shared}


def render_ext_literal_def(
    def_name: str,
    entries: tuple[tuple[str, tuple[str, ...], tuple[str, ...], int], ...],
) -> list[str]:
    """Render a pure literal `private def <def_name> : List (SigEntry × Nat)` within 100c."""
    if not entries:
        return [f"private def {def_name} : List (SigEntry × Nat) := []"]
    lines = [f"private def {def_name} : List (SigEntry × Nat) := ["]
    for idx, (nm, as_tys, rs_tys, bound) in enumerate(entries):
        comma = "," if idx + 1 < len(entries) else ""
        as_s = "[" + ", ".join(as_tys) + "]"
        rs_s = "[" + ", ".join(rs_tys) + "]"
        one = f'  (("{nm}", {as_s}, {rs_s}), {bound}){comma}'
        if len(one) <= MAX_LINE_LEN:
            lines.append(one)
        else:
            lines.append(f'  (("{nm}",')
            lines.extend(_wrap_list_elems("     ", list(as_tys), indent="      "))
            lines[-1] = lines[-1] + ","
            lines.extend(_wrap_list_elems("     ", list(rs_tys), indent="      "))
            lines[-1] = lines[-1] + f"), {bound}){comma}"
    lines.append("]")
    return lines


def render_slice(cfg: CertConfig, arch: ArchSpec, sl: SliceRange) -> str:
    """Render `<Prefix>Cert<i>.lean` for one slice `<= 12` functions."""
    fresh_slices = sum(1 for s in cfg.slices if s.reuse_src_index is None)
    ns = f"{arch.ns_prefix}.{cfg.prefix}Cert{sl.index}"
    bounds_mod = f"{arch.ns_prefix}.{cfg.prefix}Bounds"
    uses_ext = sl.start > 0
    uses_bounds_mod = uses_ext and not cfg.no_bounds_import
    cert_fns = cfg.cert_fns
    cert_src = cfg.cert_source_mod

    pub_imports = [
        "public import LeanQbe.T.MainCertCore",
        *(["public import LeanQbe.T.MainCertFlat"] if cfg.flat else []),
        f"public import {arch.lemmas_mod}",
    ]
    if uses_bounds_mod:
        pub_imports.append(f"public import {bounds_mod}")
    pub_imports.append(f"public import {cert_src}")

    meta_imports = [
        "meta import Lean",
        "meta import LeanQbe.T.MainCertElab",
        *(["meta import LeanQbe.T.MainCertFlatElab"] if cfg.flat else []),
        f"meta import {arch.targ_mod}",
    ]
    if uses_bounds_mod:
        meta_imports.append(f"meta import {bounds_mod}")
    if not is_materialized_inl_mod(cert_src):
        meta_imports.append(f"meta import {cert_src}")

    open_parts = ["LeanQbe.T", arch.ns_prefix]
    if uses_bounds_mod:
        open_parts.append(bounds_mod)
    open_parts.append(cfg.cert_source_ns)

    if sl.start == 0 and sl.end == cfg.total_fns:
        mod_rhs = cert_fns
    elif sl.start == 0:
        mod_rhs = f"{cert_fns}.take {sl.count}"
    elif sl.end == cfg.total_fns:
        mod_rhs = f"{cert_fns}.drop {sl.start}"
    else:
        mod_rhs = f"({cert_fns}.drop {sl.start}).take {sl.count}"

    abbrev_kw = "noncomputable abbrev" if is_materialized_inl_mod(cert_src) else "abbrev"
    mod_def = f"{abbrev_kw} slice{sl.index}Mod : Module := {{ fns := {mod_rhs} }}"
    if len(mod_def) > MAX_LINE_LEN:
        mod_def = (
            f"{abbrev_kw} slice{sl.index}Mod : Module :=\n"
            f"  {{ fns := {mod_rhs} }}"
        )

    mb_opt = fmt_max_bound_opt(cfg.max_bound)
    ext_def_lines: list[str] = []
    if not uses_ext:
        ext_opt = ""
    elif not cfg.no_bounds_import:
        ext_opt = f" (ext := {cfg.stem}ExtPrefix {sl.start})"
    else:
        ext_name = f"slice{sl.index}Ext"
        ext_opt = f" (ext := {ext_name})"
        arch_lits = cfg.bounds_literals.get(arch.key) if cfg.bounds_literals else None
        if arch_lits is not None and sl.index in arch_lits:
            ext_def_lines = [
                f"/-- Pruned direct-callee stack bounds for slice {sl.index} (`N2`). -/",
                *render_ext_literal_def(ext_name, arch_lits[sl.index]),
                "",
            ]
        else:
            eval_args = [
                arch.targ,
                arch.lt,
                f"({cert_fns}.take {sl.start})",
                *([mb_opt.strip()] if mb_opt else []),
                f"(pruneFor := slice{sl.index}Mod.fns)",
                *(["(flat := true)"] if cfg.flat else []),
            ]
            ext_def_lines = [
                (
                    f"-- Pruned direct-callee bounds for slice {sl.index} "
                    "(zero `*Bounds.lean` import)."
                ),
                *_wrap_lean_app(f"eval_prefix_ext! {ext_name}", eval_args, indent="  "),
                "",
            ]

    prune_opt = " (pruneExt := true)" if cfg.prune_ext else ""
    flat_opt = " (flat := true)" if cfg.flat else ""
    cmd_head = (
        f"compile_linked_chunks! cert{sl.index} {arch.targ} {arch.layout} "
        f"{arch.lt} {arch.cl}"
    )
    tail_opts = [
        f"slice{sl.index}Mod {cfg.chunk_size}",
        *([ext_opt.strip()] if ext_opt else []),
        f"(maxDirs := {cfg.max_dirs})",
        *([mb_opt.strip()] if mb_opt else []),
        *([prune_opt.strip()] if prune_opt else []),
        *([flat_opt.strip()] if flat_opt else []),
    ]
    one_tail = "  " + " ".join(tail_opts)
    if len(one_tail) <= MAX_LINE_LEN:
        cmd_tail = one_tail
    else:
        cmd_tail = "\n".join(_wrap_lean_app(f"  {tail_opts[0]}", tail_opts[1:], indent="  "))

    lines = [
        "module",
        "",
        *pub_imports,
        *meta_imports,
        "",
        "/-!",
        f"# {cfg.prefix} Certificate Slice {sl.index}/{fresh_slices} on "
        f"{arch.isa_title}",
        "",
        *wrap_comment_lines(
            f"Kernel-checked compilation cert (`cert{sl.index}`) for slice "
            f"`[{sl.start}, {sl.end})` (`{sl.count}` functions) of "
            f"`{cert_src}.{cert_fns}` on `{arch.targ}`."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(open_parts),
        "",
        f"/-- Slice {sl.index} sub-module (`[{sl.start}, {sl.end})`, "
        f"`{sl.count}` functions). -/",
        mod_def,
        "",
        *ext_def_lines,
        cmd_head,
        cmd_tail,
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def _format_cert_sig(arch: ArchSpec, mod_expr: str, max_bound: int) -> list[str]:
    """Format `LinkedCert ... <mod_expr> [] [] 0 <maxBound> :=` within 100c."""
    single = (
        f"    LinkedCert {arch.targ} {arch.layout} {arch.lt} {arch.cl} "
        f"{mod_expr} [] [] 0 {max_bound} :="
    )
    if len(single) <= MAX_LINE_LEN:
        return [single]
    return [
        f"    LinkedCert {arch.targ} {arch.layout} {arch.lt} {arch.cl}",
        f"      {mod_expr} [] [] 0 {max_bound} :=",
    ]


def _wrap_lean_app(prefix: str, args: list[str], indent: str = "    ") -> list[str]:
    """Format a Lean application on 1 line if <= `MAX_LINE_LEN`, else indented lines."""
    one = f"{prefix} " + " ".join(args)
    if len(one) <= MAX_LINE_LEN:
        return [one]
    lines = [prefix]
    cur = indent
    for a in args:
        cand = a if cur == indent else f"{cur} {a}"
        if cur == indent:
            cur = f"{indent}{a}"
        elif len(cur) + 1 + len(a) <= MAX_LINE_LEN:
            cur = f"{cur} {a}"
        else:
            lines.append(cur)
            cur = f"{indent}{a}"
    if cur != indent:
        lines.append(cur)
    return lines


def _wrap_rw_items(items: list[str], base_indent: str = "  ") -> list[str]:
    """Wrap `rw [a, b, ...]` within `MAX_LINE_LEN`."""
    one = f"{base_indent}rw [" + ", ".join(items) + "]"
    if len(one) <= MAX_LINE_LEN:
        return [one]
    cont = f"{base_indent}  "
    lines: list[str] = []
    cur = f"{base_indent}rw ["
    for idx, item in enumerate(items):
        suffix = "]" if idx == len(items) - 1 else ","
        tok = item + suffix
        sep = "" if cur.endswith("[") else " "
        if len(cur) + len(sep) + len(tok) <= MAX_LINE_LEN:
            cur = f"{cur}{sep}{tok}"
        else:
            lines.append(cur)
            cur = f"{cont}{tok}"
    lines.append(cur)
    return lines


def _wrap_list_elems(prefix: str, elems: list[str], indent: str = "    ") -> list[str]:
    """Format `[e1, e2, ...]` wrapped cleanly within `MAX_LINE_LEN`."""
    one = f"{prefix} [" + ", ".join(elems) + "]"
    if len(one) <= MAX_LINE_LEN:
        return [one]
    lines: list[str] = []
    cur = f"{prefix} ["
    for idx, el in enumerate(elems):
        suffix = "]" if idx == len(elems) - 1 else ","
        tok = el + suffix
        sep = "" if cur.endswith("[") else " "
        if len(cur) + len(sep) + len(tok) <= MAX_LINE_LEN:
            cur = f"{cur}{sep}{tok}"
        else:
            lines.append(cur)
            cur = f"{indent}{tok}"
    lines.append(cur)
    return lines


def render_cert_slices(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render standalone O(1)-boilerplate `<Prefix>Cert.lean` using `LinkedCert.ofChunkSlices`."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}Cert"
    total_slices = len(cfg.slices)
    cert_fns = cfg.cert_fns
    is_inl = cfg.is_inlined
    has_reuse = bool(cfg.reuse_prefix)
    pruned_relink = has_reuse and cfg.reuse_mode == "pruned_relink"
    bounds_mod = f"{arch.ns_prefix}.{cfg.prefix}Bounds"
    len_thm = cfg.fns_length_thm or f"{cert_fns}_length"

    def slice_mod_short(sl: SliceRange) -> str:
        if sl.reuse_src_index is not None:
            assert cfg.reuse_prefix is not None
            return f"{cfg.reuse_prefix}Cert{sl.reuse_src_index}"
        return f"{cfg.prefix}Cert{sl.index}"

    def cert_expr(sl: SliceRange) -> str:
        if has_reuse:
            k = sl.reuse_src_index if sl.reuse_src_index is not None else sl.index
            return f"{slice_mod_short(sl)}.cert{k}"
        return f"cert{sl.index}"

    def mod_expr(sl: SliceRange) -> str:
        if has_reuse:
            k = sl.reuse_src_index if sl.reuse_src_index is not None else sl.index
            return f"{slice_mod_short(sl)}.slice{k}Mod"
        return f"slice{sl.index}Mod"

    def reuse_raw_fns(sl: SliceRange) -> str:
        base_fns = cfg.reuse_inl_fns if (is_inl and cfg.reuse_inl_fns) else cert_fns
        st = sl.reuse_src_start
        if st == 0:
            return f"({base_fns}.take {sl.count})"
        return f"(({base_fns}.drop {st}).take {sl.count})"

    wf_mod = cfg.reuse_proof_mod or cfg.proof_mod
    wf_ns = cfg.reuse_proof_ns or cfg.open_proof_ns
    wf_acyc = cfg.reuse_acyclic or cfg.acyclic
    wf_thm = cfg.reuse_wf or cfg.wf
    wf_pol = cfg.reuse_inl_policy or cfg.inl_policy
    wf_inl_mod_sym = cfg.reuse_inl_mod_sym or cfg.inl_mod_sym
    wf_fns = cfg.reuse_inl_fns if (is_inl and cfg.reuse_inl_fns) else cert_fns

    pub_imports = [
        "public import LeanQbe.T.MainCertSlices",
        *(["public import LeanQbe.T.MainCertInline"] if is_inl else []),
        *(["public import LeanQbe.T.MainLinkReuseCover"] if pruned_relink else []),
        *[
            f"public import {arch.ns_prefix}.{slice_mod_short(sl)}"
            for sl in cfg.slices
        ],
        f"public import {cfg.source_mod}",
    ]
    if pruned_relink:
        pub_imports.append(f"public import {bounds_mod}")
        if wf_mod:
            pub_imports.append(f"public import {wf_mod}")
    if is_inl:
        if cfg.inl_policy_mod and cfg.inl_policy_mod != cfg.inl_mod:
            pub_imports.append(f"public import {cfg.inl_policy_mod}")
        if cfg.inl_mod:
            pub_imports.append(f"public import {cfg.inl_mod}")
    if has_reuse and cfg.reuse_inl_mod:
        pub_imports.append(f"public import {cfg.reuse_inl_mod}")
    if has_reuse and cfg.reuse_bridge_mod:
        pub_imports.append(f"public import {cfg.reuse_bridge_mod}")
    pub_imports = list(dict.fromkeys(pub_imports))

    meta_imports = [
        "meta import Lean",
        *(["meta import LeanQbe.T.MainLinkReuseElab"] if pruned_relink else []),
        f"meta import {arch.targ_mod}",
        *([] if is_materialized_inl_mod(cfg.cert_source_mod) else [f"meta import {cfg.cert_source_mod}"]),
    ]
    if pruned_relink:
        meta_imports.append(f"meta import {bounds_mod}")
    if has_reuse and cfg.reuse_inl_mod and not is_materialized_inl_mod(cfg.reuse_inl_mod):
        meta_imports.append(f"meta import {cfg.reuse_inl_mod}")
    meta_imports = list(dict.fromkeys(meta_imports))

    open_items = ["LeanQbe.T", arch.ns_prefix, cfg.open_source_ns]
    if pruned_relink:
        open_items.append(bounds_mod)
        if wf_ns:
            open_items.append(wf_ns)
    if is_inl:
        if cfg.inl_mod:
            open_items.append(cfg.inl_mod)
        if cfg.inl_policy_mod and cfg.inl_policy_mod != cfg.inl_mod:
            open_items.append(cfg.inl_policy_mod)
    if has_reuse and cfg.reuse_inl_mod:
        open_items.append(cfg.reuse_inl_mod)
    if has_reuse and cfg.reuse_bridge_mod:
        open_items.append(cfg.reuse_bridge_mod)
    open_items = list(dict.fromkeys(open_items))
    slice_ns = (
        []
        if has_reuse
        else [f"{arch.ns_prefix}.{cfg.prefix}Cert{sl.index}" for sl in cfg.slices]
    )

    slice_defs: list[str] = []
    inl_cert_name = f"{cfg.stem}InlCert"
    base_cert_name = inl_cert_name if is_inl else cfg.cert_name
    base_mod_name = cfg.inl_mod_sym if is_inl and cfg.inl_mod_sym else cfg.mod
    base_vis = "private noncomputable def" if is_inl else "noncomputable def"
    slice_ty = f"ChunkSlice {arch.targ} {arch.lt} [] 0 {cfg.max_bound} {base_mod_name}.fns"
    indexed = list(enumerate(cfg.slices, start=1))

    if pruned_relink:
        assert wf_pol is not None and wf_inl_mod_sym is not None
        if is_inl:
            slice_defs.extend(
                [
                    f"private theorem reuseBaseFns_wf : ∀ f ∈ {wf_fns}, f.Wf := by",
                    *_wrap_lean_app(
                        "  have hwf :=",
                        ["Module.optInlinePolicy_wf", wf_pol, wf_acyc, wf_thm],
                    ),
                    f"  rw [← {wf_inl_mod_sym}.eq] at hwf",
                    "  exact hwf",
                    "",
                ]
            )
        else:
            slice_defs.extend(
                [
                    f"private theorem reuseBaseFns_wf : ∀ f ∈ {wf_fns}, f.Wf :=",
                    f"  {wf_thm}",
                    "",
                ]
            )

    if has_reuse and not cfg.reuse_bridge_mod:
        assert cfg.reuse_inl_fns is not None
        for pos, sl in indexed:
            if sl.reuse_src_index is None:
                continue
            lhs_e = (
                f"{cert_fns}.take {sl.count}"
                if sl.start == 0
                else f"({cert_fns}.drop {sl.start}).take {sl.count}"
            )
            rs_st = sl.reuse_src_start
            rhs_e = (
                f"{cfg.reuse_inl_fns}.take {sl.count}"
                if rs_st == 0
                else f"({cfg.reuse_inl_fns}.drop {rs_st}).take {sl.count}"
            )
            slice_defs.extend(
                [
                    f"private theorem reuse_eq{pos} :",
                    f"    {lhs_e} = {rhs_e} := by",
                    "  t_kernel_rfl",
                ]
            )
        slice_defs.append("")

    def reuse_thm_for(pos: int, sl: SliceRange) -> str:
        if cfg.reuse_bridge_mod and cfg.reuse_thm_prefix:
            return f"{cfg.reuse_thm_prefix}{sl.reuse_src_index}"
        return f"reuse_eq{pos}"

    slice_names: list[str] = []
    for pos, sl in indexed:
        sl_nm = f"slice{pos}"
        slice_names.append(sl_nm)
        ce = cert_expr(sl)
        me = mod_expr(sl)
        if sl.reuse_src_index is not None and pruned_relink:
            rfns = reuse_raw_fns(sl)
            ext_e = f"({cfg.stem}ExtPrefix {sl.start})"
            chunk_ty = f"CompiledChunk {arch.targ} {arch.lt} [] 0"
            rthm = reuse_thm_for(pos, sl)
            slice_defs.extend(
                [
                    *_wrap_lean_app(
                        f"eval_raw_callees! rCallees{pos}", [arch.lt, rfns], indent="  "
                    ),
                    *_wrap_lean_app(
                        f"eval_pruned_ext! rExt{pos}",
                        [f"rCallees{pos}", ext_e],
                        indent="  ",
                    ),
                    f"private theorem rRaw{pos} :",
                    f"    checkRawCallsCover {arch.lt}",
                    f"      {rfns} rCallees{pos} = true := by",
                    "  t_kernel_rfl",
                    f"private theorem rCov{pos} :",
                    f"    CalleesCover {arch.lt} (chunksFns {ce}.chunks) rCallees{pos} := by",
                    f"  have hc := {ce}.fns_eq",
                    f"  dsimp only [{me}] at hc",
                    "  rw [← hc]",
                    "  exact calleesCover_of_checkRaw",
                    f"    (wf_of_take_drop {sl.reuse_src_start} {sl.count} reuseBaseFns_wf)",
                    f"    rRaw{pos}",
                    f"private theorem rAgree{pos} :",
                    f"    checkChunksExtAgreeOn rCallees{pos}",
                    f"      {ce}.chunks rExt{pos} = true := by",
                    "  t_kernel_rfl",
                    f"private noncomputable def rChunks{pos} : List ({chunk_ty}) :=",
                    *_wrap_lean_app(
                        "  relinkChunkListCover",
                        [
                            f"{ce}.chunks",
                            f"rExt{pos}",
                            f"rCallees{pos}",
                            f"rCov{pos}",
                            f"rAgree{pos}",
                        ],
                    ),
                    f"private theorem rMaxB{pos} :",
                    f"    chunksMaxBound rChunks{pos} ≤ {cfg.max_bound} := by",
                    f"  dsimp only [rChunks{pos}]",
                    "  rw [relinkChunkListCover_maxBound]",
                    f"  exact {ce}.maxBound_le",
                    f"private theorem rFnsEq{pos} :",
                    f"    ({base_mod_name}.fns.drop {sl.start}).take {sl.count} =",
                    f"      chunksFns rChunks{pos} := by",
                    f"  have hc := {ce}.fns_eq",
                    f"  dsimp only [{me}] at hc",
                    f"  dsimp only [rChunks{pos}]",
                    "  rw [relinkChunkListCover_fns, ← hc]",
                    f"  exact {rthm}",
                    f"private noncomputable def {sl_nm} :",
                    f"    {slice_ty} :=",
                    f"  {{ start := {sl.start}, count := {sl.count}, chunks := rChunks{pos},",
                    f"    fns_eq := rFnsEq{pos}, maxBound_le := rMaxB{pos} }}",
                ]
            )
        elif sl.reuse_src_index is not None:
            rthm = reuse_thm_for(pos, sl)
            slice_defs.extend(
                [
                    f"private noncomputable def {sl_nm} :",
                    f"    {slice_ty} :=",
                    f"  ChunkSlice.ofCert {sl.start} {sl.count} {ce}",
                    f"    (by first | exact {rthm} | (dsimp only [{me}]; exact {rthm}))",
                ]
            )
        elif sl.end == cfg.total_fns:
            slice_defs.extend(
                [
                    f"private noncomputable def {sl_nm} :",
                    f"    {slice_ty} :=",
                    *_wrap_lean_app(
                        "  ChunkSlice.ofDrop",
                        [
                            str(sl.start),
                            str(sl.count),
                            ce,
                            f"(by dsimp only [{base_mod_name}]; exact {len_thm})",
                            "(by decide)",
                            f"(by dsimp only [{base_mod_name}, {me}] <;> rfl)",
                        ],
                    ),
                ]
            )
        else:
            slice_defs.extend(
                [
                    f"private noncomputable def {sl_nm} :",
                    f"    {slice_ty} :=",
                    *_wrap_lean_app(
                        "  ChunkSlice.ofCert",
                        [
                            str(sl.start),
                            str(sl.count),
                            ce,
                            f"(by dsimp only [{base_mod_name}, {me}] <;> rfl)",
                        ],
                    ),
                ]
            )

    slices_list_name = f"{cfg.stem}Slices"
    sig_lines = _format_cert_sig(arch, base_mod_name, cfg.max_bound)
    use_tree = cfg.tree_groups >= 2 and len(indexed) >= 2

    if use_tree:
        n_groups = min(cfg.tree_groups, len(indexed))
        group_entries: list[str] = []
        group_slices_by_idx: list[tuple[int, list[tuple[int, SliceRange]]]] = []
        q_sz, rem_sz = divmod(len(indexed), n_groups)
        cur_p = 0
        for g_idx in range(n_groups):
            take_n = q_sz + (1 if g_idx < rem_sz else 0)
            group_slices_by_idx.append((g_idx, indexed[cur_p : cur_p + take_n]))
            cur_p += take_n

        slice_defs.append("")
        for g_idx, g_items in group_slices_by_idx:
            g_start = g_items[0][1].start
            g_end = g_items[-1][1].end
            g_count = g_end - g_start
            g_sl_names = [f"slice{p}" for p, _ in g_items]
            g_list_name = f"grp{g_idx}Slices"
            g_slice_name = f"grp{g_idx}Slice"
            g_ext_name = f"grp{g_idx}ExtIn"
            g_thm_name = f"grp{g_idx}_ext"
            ext_rhs = (
                "[]"
                if g_idx == 0
                else f"chunksNextExt grp{g_idx - 1}ExtIn grp{g_idx - 1}Slice.chunks"
            )
            slice_defs.extend(
                [
                    f"private noncomputable def {g_list_name} :",
                    f"    List ({slice_ty}) :=",
                    *_wrap_list_elems(" ", g_sl_names, indent="    "),
                    f"private noncomputable def {g_slice_name} :",
                    f"    {slice_ty} :=",
                    f"  ChunkSlice.ofSlices {g_start} {g_count} {g_list_name} (by decide)",
                    f"private noncomputable def {g_ext_name} : List (SigEntry × Nat) :=",
                    f"  {ext_rhs}",
                    f"private theorem {g_thm_name} :",
                    f"    checkChunksExt {g_ext_name} {g_slice_name}.chunks = true := by",
                    "  t_kernel_rfl",
                ]
            )
            group_entries.append(f"⟨{g_slice_name}, {g_ext_name}, {g_thm_name}⟩")

        groups_list_name = f"{cfg.stem}Groups"
        group_ty = (
            f"CheckedSliceGroup {arch.targ} {arch.lt} [] 0 {cfg.max_bound} {base_mod_name}.fns"
        )
        chain_proof = "⟨" + ", ".join(["rfl"] * n_groups + ["trivial"]) + "⟩"
        if len(chain_proof) > MAX_LINE_LEN - 6:
            chain_proof = "by repeat' constructor"
        meta_line = (
            f"    checkLinkMeta {arch.layout} "
            f"(ChunkSlice.allChunks ({groups_list_name}.map (·.slice))) = true := by"
        )
        if len(meta_line) > MAX_LINE_LEN:
            meta_line = (
                f"    checkLinkMeta {arch.layout}\n"
                f"      (ChunkSlice.allChunks ({groups_list_name}.map (·.slice))) = true := by"
            )
        of_groups_lines = _wrap_lean_app(
            "  LinkedCert.ofCheckedGroups",
            [
                groups_list_name,
                f"(by dsimp only [{base_mod_name}]; exact {len_thm})",
                "(by decide)",
                f"({chain_proof})" if " " in chain_proof else chain_proof,
                "allGroups_meta",
            ],
        )
        slice_defs.extend(
            [
                "",
                f"private noncomputable def {groups_list_name} :",
                f"    List ({group_ty}) :=",
                *_wrap_list_elems(" ", group_entries, indent="    "),
                "",
                "private theorem allGroups_meta :",
                meta_line,
                "  t_kernel_rfl",
                "",
                *wrap_comment_lines(
                    f"/-- Standalone 2-level balanced slice-tree cert ({n_groups} super-groups) "
                    f"covering all `{cfg.total_fns}` functions in `{base_mod_name}` on "
                    f"{arch.isa_title}. -/"
                ),
                f"{base_vis} {base_cert_name} :",
                *sig_lines,
                *of_groups_lines,
                "",
            ]
        )
    else:
        slice_defs.extend(
            [
                "",
                f"private noncomputable def {slices_list_name} :",
                f"    List ({slice_ty}) :=",
                *_wrap_list_elems(" ", slice_names, indent="    "),
                "",
                "private theorem allSlices_link :",
                (
                    f"    checkLinkList {arch.layout} [] "
                    f"(ChunkSlice.allChunks {slices_list_name}) = true := by"
                ),
                "  t_kernel_rfl",
                "",
            ]
        )
        if len(slice_defs[-3]) > MAX_LINE_LEN:
            slice_defs[-3] = (
                f"    checkLinkList {arch.layout} []\n"
                f"      (ChunkSlice.allChunks {slices_list_name}) = true := by"
            )

        of_slices_lines = _wrap_lean_app(
            "  LinkedCert.ofChunkSlices",
            [
                slices_list_name,
                f"(by dsimp only [{base_mod_name}]; exact {len_thm})",
                "(by decide)",
                "allSlices_link",
            ],
        )
        slice_defs.extend(
            [
                *wrap_comment_lines(
                    f"/-- Standalone kernel-checked slice-list cert covering all "
                    f"`{cfg.total_fns}` functions in `{base_mod_name}` on {arch.isa_title}. -/"
                ),
                f"{base_vis} {base_cert_name} :",
                *sig_lines,
                *of_slices_lines,
                "",
            ]
        )

    if is_inl:
        target_expr = f"({cfg.target_mod_expr})"
        cast_sig = _format_cert_sig(arch, target_expr, cfg.max_bound)
        slice_defs.extend(
            [
                *wrap_comment_lines(
                    f"/-- Full kernel-checked inlined cert over "
                    f"`{cfg.target_mod_expr}` on {arch.isa_title}, "
                    f"transported in O(1) via `LinkedCert.castModule "
                    f"{base_mod_name}.eq`. -/"
                ),
                f"noncomputable def {cfg.cert_name} :",
                *cast_sig,
                f"  {inl_cert_name}.castModule {base_mod_name}.eq",
                "",
            ]
        )

    axiom_lines: list[str] = []
    if cfg.print_axioms and worst_case_axiom_len(ns, cfg.cert_name) <= MAX_AXIOM_REPORT_LEN:
        axiom_lines = [*render_axiom_prints(ns, [cfg.cert_name]), ""]

    doc_summary = (
        f"Combines all `{total_slices}` flat 1-tier slices via "
        f"`LinkedCert.ofChunkSlices` into `{cfg.cert_name}` over "
        f"`{cfg.source_mod}.{cfg.target_mod_expr}` (`{cfg.total_fns}` functions)."
    )
    open_block = [*wrap_open_pairs(open_items)]
    if slice_ns:
        open_block.extend(wrap_open_pairs(slice_ns))

    lines = [
        "module",
        "",
        *pub_imports,
        *meta_imports,
        "",
        "/-!",
        f"# {cfg.prefix} Native Compilation Certificate on {arch.isa_title}",
        "",
        *wrap_comment_lines(doc_summary),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        *open_block,
        "",
        *slice_defs,
        *axiom_lines,
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_cert_ladder(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>Cert.lean` combining slices via single-shot `checkLinkList`."""
    if cfg.cert_style == "slices":
        return render_cert_slices(cfg, arch)
    ns = f"{arch.ns_prefix}.{cfg.prefix}Cert"
    total_slices = len(cfg.slices)
    cert_fns = cfg.cert_fns
    is_inl = cfg.is_inlined
    has_reuse = bool(cfg.reuse_prefix)
    pruned_relink = has_reuse and cfg.reuse_mode == "pruned_relink"
    bounds_mod = f"{arch.ns_prefix}.{cfg.prefix}Bounds"

    def slice_mod_short(sl: SliceRange) -> str:
        if sl.reuse_src_index is not None:
            assert cfg.reuse_prefix is not None
            return f"{cfg.reuse_prefix}Cert{sl.reuse_src_index}"
        return f"{cfg.prefix}Cert{sl.index}"

    def cert_expr(sl: SliceRange) -> str:
        if has_reuse:
            k = sl.reuse_src_index if sl.reuse_src_index is not None else sl.index
            return f"{slice_mod_short(sl)}.cert{k}"
        return f"cert{sl.index}"

    def mod_expr(sl: SliceRange) -> str:
        if has_reuse:
            k = sl.reuse_src_index if sl.reuse_src_index is not None else sl.index
            return f"{slice_mod_short(sl)}.slice{k}Mod"
        return f"slice{sl.index}Mod"

    def slice_chunks_expr(pos: int, sl: SliceRange) -> str:
        if pruned_relink and sl.reuse_src_index is not None:
            return f"rChunks{pos}"
        return f"{cert_expr(sl)}.chunks"

    def reuse_raw_fns(sl: SliceRange) -> str:
        base_fns = cfg.reuse_inl_fns if (is_inl and cfg.reuse_inl_fns) else cert_fns
        st = sl.reuse_src_start
        if st == 0:
            return f"({base_fns}.take {sl.count})"
        return f"(({base_fns}.drop {st}).take {sl.count})"

    wf_mod = cfg.reuse_proof_mod or cfg.proof_mod
    wf_ns = cfg.reuse_proof_ns or cfg.open_proof_ns
    wf_acyc = cfg.reuse_acyclic or cfg.acyclic
    wf_thm = cfg.reuse_wf or cfg.wf
    wf_pol = cfg.reuse_inl_policy or cfg.inl_policy
    wf_inl_mod_sym = cfg.reuse_inl_mod_sym or cfg.inl_mod_sym
    wf_fns = cfg.reuse_inl_fns if (is_inl and cfg.reuse_inl_fns) else cert_fns

    pub_imports = [
        "public import LeanQbe.T.MainCertInline"
        if is_inl
        else "public import LeanQbe.T.MainCertProof",
        *(["public import LeanQbe.T.MainLinkReuseCover"] if pruned_relink else []),
        *[
            f"public import {arch.ns_prefix}.{slice_mod_short(sl)}"
            for sl in cfg.slices
        ],
        f"public import {cfg.source_mod}",
    ]
    if pruned_relink:
        pub_imports.append(f"public import {bounds_mod}")
        if wf_mod:
            pub_imports.append(f"public import {wf_mod}")
    if is_inl:
        if cfg.inl_policy_mod and cfg.inl_policy_mod != cfg.inl_mod:
            pub_imports.append(f"public import {cfg.inl_policy_mod}")
        if cfg.inl_mod:
            pub_imports.append(f"public import {cfg.inl_mod}")
    if has_reuse and cfg.reuse_inl_mod:
        pub_imports.append(f"public import {cfg.reuse_inl_mod}")
    if has_reuse and cfg.reuse_bridge_mod:
        pub_imports.append(f"public import {cfg.reuse_bridge_mod}")
    pub_imports = list(dict.fromkeys(pub_imports))

    meta_imports = [
        "meta import Lean",
        *(["meta import LeanQbe.T.MainLinkReuseElab"] if pruned_relink else []),
        f"meta import {arch.targ_mod}",
        *([] if is_materialized_inl_mod(cfg.cert_source_mod) else [f"meta import {cfg.cert_source_mod}"]),
    ]
    if pruned_relink:
        meta_imports.append(f"meta import {bounds_mod}")
    if has_reuse and cfg.reuse_inl_mod and not is_materialized_inl_mod(cfg.reuse_inl_mod):
        meta_imports.append(f"meta import {cfg.reuse_inl_mod}")
    meta_imports = list(dict.fromkeys(meta_imports))

    open_items = ["LeanQbe.T", arch.ns_prefix, cfg.open_source_ns]
    if pruned_relink:
        open_items.append(bounds_mod)
        if wf_ns:
            open_items.append(wf_ns)
    if is_inl:
        if cfg.inl_mod:
            open_items.append(cfg.inl_mod)
        if cfg.inl_policy_mod and cfg.inl_policy_mod != cfg.inl_mod:
            open_items.append(cfg.inl_policy_mod)
    if has_reuse and cfg.reuse_inl_mod:
        open_items.append(cfg.reuse_inl_mod)
    if has_reuse and cfg.reuse_bridge_mod:
        open_items.append(cfg.reuse_bridge_mod)
    open_items = list(dict.fromkeys(open_items))
    slice_ns = (
        []
        if has_reuse
        else [f"{arch.ns_prefix}.{cfg.prefix}Cert{sl.index}" for sl in cfg.slices]
    )

    ladder_defs: list[str] = []
    inl_cert_name = f"{cfg.stem}InlCert"
    base_cert_name = inl_cert_name if is_inl else cfg.cert_name
    base_mod_name = cfg.inl_mod_sym if is_inl and cfg.inl_mod_sym else cfg.mod
    base_vis = "private noncomputable def" if is_inl else "noncomputable def"
    chunk_ty = f"CompiledChunk {arch.targ} {arch.lt} [] 0"
    indexed = list(enumerate(cfg.slices, start=1))

    if pruned_relink:
        if is_inl:
            assert wf_pol is not None and wf_inl_mod_sym is not None
            ladder_defs.extend(
                [
                    f"private theorem reuseBaseFns_wf : ∀ f ∈ {wf_fns}, f.Wf := by",
                    *_wrap_lean_app(
                        "  have hwf :=",
                        ["Module.optInlinePolicy_wf", wf_pol, wf_acyc, wf_thm],
                    ),
                    f"  rw [← {wf_inl_mod_sym}.eq] at hwf",
                    "  exact hwf",
                    "",
                ]
            )
        else:
            ladder_defs.extend(
                [
                    f"private theorem reuseBaseFns_wf : ∀ f ∈ {wf_fns}, f.Wf :=",
                    f"  {wf_thm}",
                    "",
                ]
            )

        for pos, sl in indexed:
            if sl.reuse_src_index is None:
                continue
            rfns = reuse_raw_fns(sl)
            ce = cert_expr(sl)
            me = mod_expr(sl)
            ext_e = f"({cfg.stem}ExtPrefix {sl.start})"
            ladder_defs.extend(
                [
                    *_wrap_lean_app(
                        f"eval_raw_callees! rCallees{pos}", [arch.lt, rfns], indent="  "
                    ),
                    *_wrap_lean_app(
                        f"eval_pruned_ext! rExt{pos}", [f"rCallees{pos}", ext_e], indent="  "
                    ),
                    f"private theorem rRaw{pos} :",
                    f"    checkRawCallsCover {arch.lt}",
                    f"      {rfns} rCallees{pos} = true := by",
                    "  t_kernel_rfl",
                    f"private theorem rCov{pos} :",
                    f"    CalleesCover {arch.lt} (chunksFns {ce}.chunks) rCallees{pos} := by",
                    f"  have hc := {ce}.fns_eq",
                    f"  dsimp only [{me}] at hc",
                    "  rw [← hc]",
                    "  exact calleesCover_of_checkRaw",
                    f"    (wf_of_take_drop {sl.reuse_src_start} {sl.count} reuseBaseFns_wf)",
                    f"    rRaw{pos}",
                    f"private theorem rAgree{pos} :",
                    f"    checkChunksExtAgreeOn rCallees{pos}",
                    f"      {ce}.chunks rExt{pos} = true := by",
                    "  t_kernel_rfl",
                    f"private noncomputable def rChunks{pos} : List ({chunk_ty}) :=",
                    *_wrap_lean_app(
                        "  relinkChunkListCover",
                        [
                            f"{ce}.chunks",
                            f"rExt{pos}",
                            f"rCallees{pos}",
                            f"rCov{pos}",
                            f"rAgree{pos}",
                        ],
                    ),
                    f"private theorem rMaxB{pos} :",
                    f"    chunksMaxBound rChunks{pos} ≤ {cfg.max_bound} := by",
                    f"  dsimp only [rChunks{pos}]",
                    "  rw [relinkChunkListCover_maxBound]",
                    f"  exact {ce}.maxBound_le",
                    "",
                ]
            )

    def maxb_thm_for(pos: int, sl: SliceRange) -> str:
        if pruned_relink and sl.reuse_src_index is not None:
            return f"rMaxB{pos}"
        return f"{cert_expr(sl)}.maxBound_le"

    if total_slices == 1:
        sl0 = cfg.slices[0]
        sig_lines = _format_cert_sig(arch, base_mod_name, cfg.max_bound)
        if pruned_relink and sl0.reuse_src_index is not None:
            ce0 = cert_expr(sl0)
            me0 = mod_expr(sl0)
            ladder_defs.extend(
                [
                    "private theorem singleLink :",
                    f"    checkLinkList {arch.layout} [] rChunks1 = true := by",
                    "  t_kernel_rfl",
                    "private theorem singleFnsEq :",
                    f"    {base_mod_name}.fns = chunksFns rChunks1 := by",
                    f"  have hc := {ce0}.fns_eq",
                    f"  dsimp only [{me0}] at hc",
                    "  dsimp only [rChunks1]",
                    "  rw [relinkChunkListCover_fns, ← hc]",
                    f"  dsimp only [{base_mod_name}]",
                    "  rfl",
                    *wrap_comment_lines(
                        f"/-- Full kernel-checked cert covering `{cfg.total_fns}` "
                        f"functions in `{base_mod_name}` on {arch.isa_title}. -/"
                    ),
                    f"{base_vis} {base_cert_name} :",
                    *sig_lines,
                    "  { chunks := rChunks1",
                    "    linkCheck := singleLink",
                    "    fns_eq := singleFnsEq",
                    "    supportsAll := supportsAll_of_eq singleFnsEq",
                    "      (supportsAll_of_chunks rChunks1)",
                    "    maxBound_le := rMaxB1 }",
                    "",
                ]
            )
        else:
            if is_inl:
                rhs_lines = [
                    f"  {cert_expr(sl0)}.castFns (by dsimp only [{mod_expr(sl0)}, {cert_fns}]; rfl)"
                ]
            else:
                rhs_lines = [f"  {cert_expr(sl0)}"]
            ladder_defs.extend(
                [
                    f"/-- Full kernel-checked cert covering `{cfg.total_fns}` "
                    f"functions in `{base_mod_name}` on {arch.isa_title}. -/",
                    f"{base_vis} {base_cert_name} :",
                    *sig_lines,
                    *rhs_lines,
                    "",
                ]
            )
    else:
        last_pos, last_sl = indexed[-1]
        def chunk_name(pos: int) -> str:
            return "allChunks" if pos == 1 else f"sufChunks{pos}"

        def fmt_chunk_def(nm: str, rhs: str) -> list[str]:
            single = f"private noncomputable def {nm} : List ({chunk_ty}) := {rhs}"
            if len(single) <= MAX_LINE_LEN:
                return [single]
            return [
                f"private noncomputable def {nm} :",
                f"    List ({chunk_ty}) :=",
                f"  {rhs}",
            ]

        ladder_defs.extend(
            fmt_chunk_def(chunk_name(last_pos), slice_chunks_expr(last_pos, last_sl))
        )
        for pos, sl in reversed(indexed[:-1]):
            ladder_defs.extend(
                fmt_chunk_def(
                    chunk_name(pos),
                    f"{slice_chunks_expr(pos, sl)} ++ {chunk_name(pos + 1)}",
                )
            )
        ladder_defs.append("")

        ladder_defs.extend(
            [
                "private theorem allChunks_link :",
                f"    checkLinkList {arch.layout} [] allChunks = true := by",
                "  t_kernel_rfl",
                "",
            ]
        )

        if has_reuse and not cfg.reuse_bridge_mod:
            assert cfg.reuse_inl_fns is not None
            for pos, sl in indexed:
                if sl.reuse_src_index is None:
                    continue
                lhs_e = (
                    f"{cert_fns}.take {sl.count}"
                    if sl.start == 0
                    else f"({cert_fns}.drop {sl.start}).take {sl.count}"
                )
                rs_st = sl.reuse_src_start
                rhs_e = (
                    f"{cfg.reuse_inl_fns}.take {sl.count}"
                    if rs_st == 0
                    else f"({cfg.reuse_inl_fns}.drop {rs_st}).take {sl.count}"
                )
                ladder_defs.extend(
                    [
                        f"private theorem reuse_eq{pos} :",
                        f"    {lhs_e} = {rhs_e} := by",
                        "  t_kernel_rfl",
                    ]
                )
            ladder_defs.append("")

        def reuse_thm_for(pos: int, sl: SliceRange) -> str:
            if cfg.reuse_bridge_mod and cfg.reuse_thm_prefix:
                return f"{cfg.reuse_thm_prefix}{sl.reuse_src_index}"
            return f"reuse_eq{pos}"

        last_nm = chunk_name(last_pos)
        last_sig = (
            f"private theorem fns_eq{last_pos} : "
            f"{cert_fns}.drop {last_sl.start} = chunksFns {last_nm} := by"
        )
        if len(last_sig) > MAX_LINE_LEN:
            last_sig = (
                f"private theorem fns_eq{last_pos} :\n"
                f"    {cert_fns}.drop {last_sl.start} = chunksFns {last_nm} := by"
            )
        if pruned_relink and last_sl.reuse_src_index is not None:
            rthm_last = reuse_thm_for(last_pos, last_sl)
            ladder_defs.extend(
                [
                    last_sig,
                    f"  have hc := {cert_expr(last_sl)}.fns_eq",
                    f"  dsimp only [{mod_expr(last_sl)}] at hc",
                    f"  dsimp only [{last_nm}, rChunks{last_pos}]",
                    "  rw [relinkChunkListCover_fns, ← hc]",
                    f"  exact {rthm_last}.symm",
                ]
            )
        else:
            ladder_defs.extend(
                [
                    last_sig,
                    f"  have hc := {cert_expr(last_sl)}.fns_eq",
                    f"  dsimp only [{mod_expr(last_sl)}] at hc",
                    "  exact hc",
                ]
            )
        for pos, sl in reversed(indexed[1:-1]):
            nm = chunk_name(pos)
            sig = (
                f"private theorem fns_eq{pos} : "
                f"{cert_fns}.drop {sl.start} = chunksFns {nm} := by"
            )
            if len(sig) > MAX_LINE_LEN:
                sig = (
                    f"private theorem fns_eq{pos} :\n"
                    f"    {cert_fns}.drop {sl.start} = chunksFns {nm} := by"
                )
            use_pruned = pruned_relink and sl.reuse_src_index is not None
            rw_items = ([] if use_pruned else [nm]) + ["chunksFns_append"]
            if use_pruned:
                rw_items.append("relinkChunkListCover_fns")
            rw_items.extend([f"← fns_eq{pos + 1}", "← hc"])
            if sl.reuse_src_index is not None:
                rw_items.append(f"← {reuse_thm_for(pos, sl)}")
            drop_ln = f"  exact (drop_take_append_drop {cert_fns} {sl.start} {sl.count}).symm"
            if len(drop_ln) > MAX_LINE_LEN:
                drop_ln = (
                    f"  exact (drop_take_append_drop {cert_fns}\n"
                    f"    {sl.start} {sl.count}).symm"
                )
            dsimp_lns = [f"  dsimp only [{nm}, rChunks{pos}]"] if use_pruned else []
            ladder_defs.extend(
                [
                    sig,
                    f"  have hc := {cert_expr(sl)}.fns_eq",
                    f"  dsimp only [{mod_expr(sl)}] at hc",
                    *dsimp_lns,
                    *_wrap_rw_items(rw_items),
                    drop_ln,
                ]
            )
        sl1 = cfg.slices[0]
        h1_ln = f"  have h1 : {cert_fns} = chunksFns allChunks := by"
        if len(h1_ln) > MAX_LINE_LEN:
            h1_ln = f"  have h1 :\n      {cert_fns} = chunksFns allChunks := by"
        take_ln = f"    exact (List.take_append_drop {sl1.count} {cert_fns}).symm"
        if len(take_ln) > MAX_LINE_LEN:
            take_ln = (
                f"    exact (List.take_append_drop {sl1.count}\n"
                f"      {cert_fns}).symm"
            )
        use_pruned1 = pruned_relink and sl1.reuse_src_index is not None
        rw1_items = ["chunksFns_append"]
        if use_pruned1:
            rw1_items.append("relinkChunkListCover_fns")
        rw1_items.extend(["← fns_eq2", "← hc"])
        if sl1.reuse_src_index is not None:
            rw1_items.append(f"← {reuse_thm_for(1, sl1)}")
        dsimp1_ln = (
            "    dsimp only [allChunks, rChunks1]"
            if use_pruned1
            else "    dsimp only [allChunks]"
        )
        ladder_defs.extend(
            [
                "private theorem allChunks_fns_eq :",
                f"    {base_mod_name}.fns = chunksFns allChunks := by",
                f"  have hc := {cert_expr(sl1)}.fns_eq",
                f"  dsimp only [{mod_expr(sl1)}] at hc",
                h1_ln,
                dsimp1_ln,
                *_wrap_rw_items(rw1_items, base_indent="    "),
                take_ln,
                "  exact h1",
                "",
            ]
        )

        ladder_defs.extend(
            [
                f"private theorem maxB{last_pos} :",
                f"    chunksMaxBound {last_nm} ≤ {cfg.max_bound} :=",
                f"  {maxb_thm_for(last_pos, last_sl)}",
            ]
        )
        for pos, sl in reversed(indexed[:-1]):
            nm = chunk_name(pos)
            thm = "allChunks_maxBound" if pos == 1 else f"maxB{pos}"
            max_sig = (
                f"private theorem {thm} : chunksMaxBound {nm} ≤ {cfg.max_bound} := by"
            )
            if len(max_sig) > MAX_LINE_LEN:
                max_sig = (
                    f"private theorem {thm} :\n"
                    f"    chunksMaxBound {nm} ≤ {cfg.max_bound} := by"
                )
            mb_ref = maxb_thm_for(pos, sl)
            app_ln = f"    chunksMaxBound_append_le {mb_ref} maxB{pos + 1}"
            if len(app_ln) > MAX_LINE_LEN:
                app_ln = (
                    f"    chunksMaxBound_append_le {mb_ref}\n"
                    f"      maxB{pos + 1}"
                )
            ladder_defs.extend(
                [
                    max_sig,
                    f"  rw [{nm}]",
                    "  simpa only [Nat.max_self] using",
                    app_ln,
                ]
            )
        ladder_defs.append("")

        sig_lines = _format_cert_sig(arch, base_mod_name, cfg.max_bound)
        supp_ln = (
            "    supportsAll := supportsAll_of_eq allChunks_fns_eq "
            "(supportsAll_of_chunks allChunks)"
        )
        if len(supp_ln) > MAX_LINE_LEN:
            supp_ln = (
                "    supportsAll := supportsAll_of_eq allChunks_fns_eq\n"
                "      (supportsAll_of_chunks allChunks)"
            )
        ladder_defs.extend(
            [
                *wrap_comment_lines(
                    f"/-- Full kernel-checked cert covering all "
                    f"`{cfg.total_fns}` functions in `{base_mod_name}` on "
                    f"{arch.isa_title}. -/"
                ),
                f"{base_vis} {base_cert_name} :",
                *sig_lines,
                "  { chunks := allChunks",
                "    linkCheck := allChunks_link",
                "    fns_eq := allChunks_fns_eq",
                supp_ln,
                "    maxBound_le := allChunks_maxBound }",
                "",
            ]
        )

    if is_inl:
        target_expr = f"({cfg.target_mod_expr})"
        cast_sig = _format_cert_sig(arch, target_expr, cfg.max_bound)
        ladder_defs.extend(
            [
                *wrap_comment_lines(
                    f"/-- Full kernel-checked inlined cert over "
                    f"`{cfg.target_mod_expr}` on {arch.isa_title}, "
                    f"transported in O(1) via `LinkedCert.castModule "
                    f"{base_mod_name}.eq`. -/"
                ),
                f"noncomputable def {cfg.cert_name} :",
                *cast_sig,
                f"  {inl_cert_name}.castModule {base_mod_name}.eq",
                "",
            ]
        )

    axiom_lines: list[str] = []
    if cfg.print_axioms and worst_case_axiom_len(ns, cfg.cert_name) <= MAX_AXIOM_REPORT_LEN:
        axiom_lines = [*render_axiom_prints(ns, [cfg.cert_name]), ""]

    reused_cnt = sum(1 for s in cfg.slices if s.reuse_src_index is not None)
    fresh_cnt = total_slices - reused_cnt
    reuse_desc = "callee-pruned relinked" if pruned_relink else "verbatim reused"
    doc_summary = (
        f"Combines `{fresh_cnt}` fresh `{cfg.prefix}Cert1..{fresh_cnt}` slices and "
        f"`{reused_cnt}` {reuse_desc} `{cfg.reuse_prefix}Cert*` slices via "
        f"a single-shot `checkLinkList` proof into `{cfg.cert_name}` over "
        f"`{cfg.source_mod}.{cfg.target_mod_expr}` (`{cfg.total_fns}` functions)."
        if has_reuse
        else (
            f"Combines all `{total_slices}` flat 1-tier slices "
            f"(`{cfg.prefix}Cert1`..`{cfg.prefix}Cert{total_slices}`) via "
            f"a single-shot `checkLinkList` proof into `{cfg.cert_name}` over "
            f"`{cfg.source_mod}.{cfg.target_mod_expr}` (`{cfg.total_fns}` functions)."
        )
    )
    open_block = [*wrap_open_pairs(open_items)]
    if slice_ns:
        open_block.extend(wrap_open_pairs(slice_ns))

    lines = [
        "module",
        "",
        *pub_imports,
        *meta_imports,
        "",
        "/-!",
        f"# {cfg.prefix} Native Compilation Certificate on {arch.isa_title}",
        "",
        *wrap_comment_lines(doc_summary),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        *open_block,
        "",
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
    if cfg.abi_common:
        abi_args = (
            "⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp"
            if arch.key == "amd64"
            else "⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩"
        )
        solve_body = [
            "  refine eventually_weaken _ _ _ _",
            "    (fun _ ⟨hpc, ⟨hcal, hsp'⟩, m', hQ, hm'⟩ => ⟨hpc, hcal, hsp', m', hQ, hm'⟩)",
            *_wrap_lean_app(
                "    (Examples.Kissat.KissatCertCommon.solve_of_abi_fnspec",
                [
                    arch.kissat_abi,
                    "hh",
                    f'"{cfg.entry_fn}"',
                    "hfnspec",
                    "cnf_ptr",
                    "cnf_len",
                    "work_ptr",
                    "work_len",
                    "fuel",
                    "hspec",
                    "s",
                    "ra",
                    "R",
                    abi_args,
                    "hmem)",
                ],
                indent="      ",
            ),
        ]
    else:
        solve_body = [
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
    solve_block = [
        f"/-- Lifting any `FnSpec` for `\"{cfg.entry_fn}\"` at stack bound "
        "`b` and contract",
        f"`spec` to {arch.kraken_isa} `Eventually` via `{arch.of_returns_fn}`. -/",
        *solve_sig_lines[:-1],
        f"{solve_sig_lines[-1]} := by",
        *solve_body,
    ]

    if cfg.is_inlined:
        mk_fnspec_lines = [
            f"/-- Generic `FnSpec` for every function in `{cfg.mod}` compiled under",
            f"`{cfg.inl_policy}` on `{arch.targ}`, lifted from source `ModuleOk Γ {cfg.mod}`.",
            "-/",
            "theorem mk_module_fnspec (Γ : Env)",
            f"    (hM : ModuleOk Γ {cfg.mod})",
            f"    (hnoex : ∀ g ∈ {cfg.fns}, ∀ args m Q X X',",
            "      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')",
            f"    (k₀ : Nat) (hc : {cfg.cert_name}.code.IsInfixAt Host.prog k₀)",
            "    (hu : Host.LabelsUnique)",
            f"    {{f : Fn}} (hf : f ∈ {cfg.mod}.fns) :",
            f"    {arch.targ}.Defined hh f.name ∧",
            f"      {arch.targ}.FnSpec hh f.name (Γ f.name f.as f.rs) "
            f"({cfg.cert_name}.bound f.name) 0 :=",
            f"  {cfg.cert_name}.fnSpec_noExit_of_legalSigAll_optInlinePolicy hh Γ k₀ hc hu",
            f"    hM {cfg.legal_sig} hf (hnoex f hf)",
        ]
    else:
        mk_fnspec_lines = [
            f"/-- Generic `FnSpec` for every function in `{cfg.mod}` on `{arch.targ}`, "
            "parameterized over a",
            "sound environment `Γ` whose contracts ignore exit continuations. -/",
            "theorem mk_module_fnspec (Γ : Env)",
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
        ]

    # Single-line `< 115c` axiom audit: alias long names when needed.
    legal_alias_lines: list[str] = []
    axiom_section: list[str] = []
    if cfg.print_axioms:
        audit_names: list[str] = []
        if worst_case_axiom_len(ns, cfg.legal_sig) <= MAX_AXIOM_REPORT_LEN:
            audit_names.append(cfg.legal_sig)
        elif worst_case_axiom_len(ns, "ax_legal") <= MAX_AXIOM_REPORT_LEN:
            legal_alias_lines = [
                "",
                f"theorem ax_legal : LegalSigAll {arch.lt} {cfg.fns} :=",
                f"  {cfg.legal_sig}",
            ]
            audit_names.append("ax_legal")
        if worst_case_axiom_len(ns, "mk_module_fnspec") <= MAX_AXIOM_REPORT_LEN:
            audit_names.append("mk_module_fnspec")
        elif worst_case_axiom_len(ns, "ax_fnspec") <= MAX_AXIOM_REPORT_LEN:
            if cfg.is_inlined:
                fnspec_alias_lines = [
                    "",
                    "theorem ax_fnspec (Γ : Env)",
                    f"    (hM : ModuleOk Γ {cfg.mod})",
                    f"    (hnoex : ∀ g ∈ {cfg.fns}, ∀ args m Q X X',",
                    "      Γ g.name g.as g.rs args m Q X → Γ g.name g.as g.rs args m Q X')",
                    f"    (k₀ : Nat) (hc : {cfg.cert_name}.code.IsInfixAt Host.prog k₀)",
                    "    (hu : Host.LabelsUnique)",
                    f"    {{f : Fn}} (hf : f ∈ {cfg.mod}.fns) :",
                    f"    {arch.targ}.Defined hh f.name ∧",
                    f"      {arch.targ}.FnSpec hh f.name (Γ f.name f.as f.rs) "
                    f"({cfg.cert_name}.bound f.name) 0 :=",
                    "  mk_module_fnspec Γ hM hnoex k₀ hc hu hf",
                ]
            else:
                fnspec_alias_lines = [
                    "",
                    "theorem ax_fnspec (Γ : Env)",
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
                    "  mk_module_fnspec Γ hsound hnoex k₀ hc hu hf",
                ]
            mk_fnspec_lines.extend(fnspec_alias_lines)
            audit_names.append("ax_fnspec")
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

    link_pub_imports = [f"public import {cert_mod}"]
    link_priv_imports: list[str] = []
    link_open_items = ["LeanQbe.T", arch.ns_prefix, cert_mod, cfg.open_source_ns]
    if cfg.abi_common:
        link_pub_imports.append(
            "public import LeanQbe.T.Examples.Kissat.KissatCertCommon"
        )
        link_priv_imports.append(f"import {arch.ns_prefix}.KissatAbi")
        link_open_items.append("LeanQbe.T.Examples.Kissat.KissatCertCommon")
    link_open_items.append("Kraken")
    link_priv_imports.extend(["import Kraken.Mem", "import Kraken.Separation"])

    lines = [
        "module",
        "",
        *link_pub_imports,
        *link_priv_imports,
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
        "public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(link_open_items),
        "",
        f"private theorem {cfg.stem}_legalSig_check :",
        f"    checkLegalSigAll {arch.lt} {cfg.fns} = true := by",
        "  t_kernel_rfl",
        "",
        f"/-- All `{cfg.total_fns}` function signatures in `{cfg.fns}` satisfy "
        f"`{arch.lt}.legalSig`. -/",
        f"theorem {cfg.legal_sig} : LegalSigAll {arch.lt} {cfg.fns} :=",
        f"  legalSigAll_of_check {cfg.stem}_legalSig_check",
        *legal_alias_lines,
        "",
        "section Generic",
        "variable [hh : Host]",
        "",
        *mk_fnspec_lines,
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
        f"{cfg.target_mod_expr}{bound_suffix}"
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
            f"      ({cfg.target_mod_expr}){bound_suffix} :=",
            f"  {cfg.prefix}Cert.{cfg.cert_name}",
        ]

    pub_imports = [
        f"public import {cert_mod}",
        f"public import {link_mod}",
    ]
    if cfg.wrapper_mode != "compiled":
        pub_imports.append(f"public import {cfg.proof_mod}")
    priv_imports: list[str] = [f"import {arch.lemmas_mod}"]
    abi_full = cfg.abi_common and cfg.wrapper_mode == "full" and cfg.hdr_model == "m6"
    if abi_full:
        pub_imports.append("public import LeanQbe.T.Examples.Kissat.KissatCertCommon")
        priv_imports.append(f"import {arch.ns_prefix}.KissatAbi")
    if cfg.wrapper_mode == "full" and cfg.hdr_model == "m6":
        sound_mod = (
            cfg.sat_sound_mod
            if cfg.sat_sound_mod is not None
            else "LeanQbe.T.Examples.Kissat.FullM6SatSound"
        )
        nv_mod = cfg.sat_nv_mod or "LeanQbe.T.Examples.Kissat.FullM6SatNv"
        if cfg.emit_sound:
            if sound_mod:
                pub_imports.append(f"public import {sound_mod}")
            pub_imports.append(f"public import {nv_mod}")
        elif not abi_full:
            if sound_mod:
                priv_imports.append(f"import {sound_mod}")
            priv_imports.append(f"import {nv_mod}")
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
        cfg.open_source_ns,
        arch.ns_prefix,
        link_mod,
        "Kraken",
    ]
    if abi_full:
        open_parts.append("LeanQbe.T.Examples.Kissat.KissatCertCommon")
    if cfg.wrapper_mode == "full" and cfg.hdr_model == "m6":
        open_parts.extend(
            [
                "LeanQbe.T.Examples.Kissat.FullM6",
                "LeanQbe.T.Examples.Kissat.FullM6Hdr",
                "LeanQbe.T.Examples.Kissat.FullM6Orch",
                cfg.open_proof_ns,
            ]
        )
        if not cfg.source_ns:
            open_parts.append(cfg.proof_mod)
    if cfg.wrapper_mode == "full" and (
        cfg.entry_const.startswith("Full.") or cfg.hdr_model == "m6"
    ):
        open_parts.append("LeanQbe.T.Examples.Kissat.Full")
    if cfg.inl_policy_mod:
        open_parts.append(cfg.inl_policy_mod)
    open_parts = list(dict.fromkeys(open_parts))

    body: list[str] = [
        *wrap_comment_lines(
            f"/-- Compiled `LinkedCert` for `{cfg.target_mod_expr}` (`{cfg.total_fns}` "
            f"functions) on {arch.isa_title}. -/"
        ),
        *compiled_decl,
        "",
    ]

    abi_full = cfg.abi_common and cfg.wrapper_mode == "full" and cfg.hdr_model == "m6"
    if cfg.wrapper_mode == "full":
        if cfg.solve_mem_thm:
            solve_in_lines = [
                f"theorem solve_in_{cfg.mod} :",
                f"    {cfg.entry_const} ∈ {cfg.mod}.fns :=",
                f"  {cfg.solve_mem_thm}",
            ]
        else:
            solve_in_lines = [
                f"theorem solve_in_{cfg.mod} :",
                f"    {cfg.entry_const} ∈ {cfg.mod}.fns := by",
                "  exact List.mem_of_getElem?",
                f"    (by t_kernel_rfl : ({cfg.mod}.fns)[{cfg.entry_idx}]? = "
                f"some {cfg.entry_const})",
            ]
    else:
        solve_in_lines = []

    pkg_lines: list[str] = []
    unsat_pkg = f"{cfg.stem}UnsatPkg"
    nv_unsat_pkg = unsat_pkg
    if abi_full:
        assert cfg.inl_policy is not None
        def _mk_unsat_pkg_lines(
            pkg_nm: str, env_nm: str, mod_ok_nm: str, no_ex_nm: str
        ) -> list[str]:
            if cfg.solve_spec_has_sat:
                spec_cb = [
                    "        (fun r m' hdom hu _ htr hm' =>",
                    "          hreq r m' hdom hu htr hm'))",
                ]
            else:
                spec_cb = []
            if not spec_cb:
                intro_lines = _wrap_lean_app(
                    f"      ({cfg.solve_spec_intro}",
                    ["hcfit", "hwfit", "hm", "hreq)"],
                    indent="        ",
                )
            else:
                intro_lines = [
                    f"      ({cfg.solve_spec_intro} hcfit hwfit hm",
                    *spec_cb,
                ]
            return [
                f"private def {pkg_nm} : KissatUnsatPkg where",
                f"  mod := {cfg.mod}",
                f"  inlPolicy := {cfg.inl_policy}",
                f'  entryFn := "{cfg.entry_fn}"',
                f"  entryFn_fn := {cfg.entry_const}",
                "  entryFn_sig := ⟨rfl, rfl, rfl⟩",
                f"  entry_mem := solve_in_{cfg.mod}",
                f"  env := {env_nm}",
                f"  moduleOk := {mod_ok_nm}",
                f"  noExit := fun g _ => {no_ex_nm} g.name g.as g.rs",
                "  solve_intro hcfit hwfit hm hreq :=",
                f"    {env_nm}{cfg.solve_bytes_suffix}",
                *intro_lines,
                "",
            ]

        pkg_lines.extend(
            [
                *solve_in_lines,
                "",
                *_mk_unsat_pkg_lines(
                    unsat_pkg, cfg.env, cfg.module_ok, cfg.no_exit
                ),
            ]
        )
        if (
            cfg.unsat_env != cfg.env
            or cfg.unsat_module_ok != cfg.module_ok
            or cfg.unsat_no_exit != cfg.no_exit
        ):
            nv_unsat_pkg = f"{cfg.stem}NvUnsatPkg"
            pkg_lines.extend(
                _mk_unsat_pkg_lines(
                    nv_unsat_pkg,
                    cfg.unsat_env,
                    cfg.unsat_module_ok,
                    cfg.unsat_no_exit,
                )
            )
        body.extend(pkg_lines)

    fnspec_thm = f"{cfg.stem}_module_fnspec"
    if cfg.wrapper_mode in ("fnspec", "full"):
        if abi_full:
            mk_call = _wrap_lean_app(
                "  Examples.Kissat.KissatCertCommon.module_fnspec_of_abi",
                [
                    arch.kissat_abi,
                    unsat_pkg,
                    compiled_name,
                    cfg.legal_sig,
                    "hh",
                    "k₀",
                    "hc",
                    "hu",
                    "hf",
                ],
                indent="    ",
            )
        elif cfg.is_inlined:
            mk_call = [
                f"  {cfg.prefix}CertLink.mk_module_fnspec {cfg.env} {cfg.module_ok}",
                f"    (fun g _ => {cfg.no_exit} g.name g.as g.rs) k₀ hc hu hf",
            ]
        else:
            mk_call = [
                f"  {cfg.prefix}CertLink.mk_module_fnspec {cfg.env}",
                "    (fun g hg args m Q X hs => by",
                "      obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg",
                f"      exact ({cfg.module_ok}.fnsOk pre g post hsp).2.2 args m Q X hs)",
                f"    (fun g _ => {cfg.no_exit} g.name g.as g.rs) k₀ hc hu hf",
            ]
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
                *mk_call,
                "",
            ]
        )

    unsat_audit: list[str] = []
    if cfg.wrapper_mode == "full":
        if cfg.hdr_model == "m6":
            unsat_lines, unsat_audit = render_m6_unsat_section(
                cfg,
                arch,
                compiled_name,
                ns,
                unsat_pkg=unsat_pkg,
                nv_unsat_pkg=nv_unsat_pkg,
            )
            extra_helpers: list[str] = []
        else:
            unsat_lines, unsat_audit = render_unsat_section(
                cfg, arch, compiled_name, ns
            )
            extra_helpers = [
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
            ]
        if abi_full:
            body.extend(unsat_lines)
        else:
            body.extend(
                [
                    *solve_in_lines,
                    "",
                    *extra_helpers,
                    "theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}",
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
        elif worst_case_axiom_len(ns, "ax_compiled") <= MAX_AXIOM_REPORT_LEN:
            body.extend(
                [
                    f"noncomputable abbrev ax_compiled := {compiled_name}",
                    "",
                ]
            )
            audit_names.append("ax_compiled")
        if cfg.wrapper_mode in ("fnspec", "full"):
            if worst_case_axiom_len(ns, fnspec_thm) <= MAX_AXIOM_REPORT_LEN:
                audit_names.append(fnspec_thm)
            elif worst_case_axiom_len(ns, "ax_fnspec") <= MAX_AXIOM_REPORT_LEN:
                body.extend(
                    [
                        "theorem ax_fnspec [hh : Host] (k₀ : Nat)",
                        f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
                        "    (hu : Host.LabelsUnique)",
                        f"    {{f : Fn}} (hf : f ∈ {cfg.mod}.fns) :",
                        f"    {arch.targ}.Defined hh f.name ∧",
                        f"      {arch.targ}.FnSpec hh f.name ({cfg.env} f.name f.as f.rs)",
                        f"        ({compiled_name}.bound f.name) 0 :=",
                        f"  {fnspec_thm} k₀ hc hu hf",
                        "",
                    ]
                )
                audit_names.append("ax_fnspec")
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
        "public section",
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


def _render_nv_payload_helpers(stem: str) -> list[str]:
    """Emit shared `6,144 B` `M6Hdr` non-vacuity payload helpers (`<= 8192 B` `TargetInit`)."""
    return [
        f"def {stem}NvWorkLen : Nat := {M6_NV_WORK_LEN}",
        "",
        f"theorem {stem}NvWorkLen_eq : {stem}NvWorkLen = {M6_NV_WORK_LEN} := by",
        f"  unfold {stem}NvWorkLen; rfl",
        "",
        f"def {stem}NvPayload (cnfBytes : List UInt8) : List UInt8 :=",
        f"  cnfBytes ++ List.replicate {stem}NvWorkLen 0",
        "",
        f"theorem {stem}NvPayload_eq (cnfBytes : List UInt8) :",
        f"    {stem}NvPayload cnfBytes =",
        f"      cnfBytes ++ List.replicate {M6_NV_WORK_LEN} 0 := by",
        f"  unfold {stem}NvPayload {stem}NvWorkLen; rfl",
        "",
        f"theorem {stem}NvPayload_length (cnfBytes : List UInt8) :",
        f"    ({stem}NvPayload cnfBytes).length = cnfBytes.length + {stem}NvWorkLen := by",
        f"  simp only [{stem}NvPayload, List.length_append, List.length_replicate]",
        "",
        f"theorem {stem}NvPayload_sep (cnfBytes : List UInt8) "
        "(hcb : cnfBytes.length ≤ 2048) :",
        f"    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) {stem}NvWorkLen)",
        f"      (({stem}NvPayload cnfBytes).At nvM6CnfPtr) :=",
        "  nv_sep_append rfl",
        f"    (by unfold {stem}NvWorkLen; rw [List.length_replicate]; omega)",
        f"    rfl ⟨List.replicate {stem}NvWorkLen 0, List.length_replicate, rfl⟩",
        "",
        f"theorem {stem}Nv_unsat_bound :",
        f"    fullM6ExtBytes + fullFixedBytes 1 + 2 * 40 + 136 + 8 ≤ {stem}NvWorkLen := by",
        f"  unfold {stem}NvWorkLen fullM6ExtBytes fullFixedBytes valsBytes markBytes",
        "    u32FullBytes fullMinDepthOf",
        "  decide",
        "",
    ]


def render_m6_unsat_section(
    cfg: CertConfig,
    arch: ArchSpec,
    compiled_name: str,
    ns: str,
    unsat_pkg: str = "",
    nv_unsat_pkg: str = "",
) -> tuple[list[str], list[str]]:
    """Render `432`-word `FullM6Hdr` UNSAT soundness and concrete non-vacuity wrappers."""
    unsat_thm = f"{cfg.stem}_solve_bytes_unsat_{arch.arch_tag}"
    sound_thm = f"kissat_{cfg.stem}_{arch.arch_tag}_unsat_correct"
    nv_thm = f"{cfg.stem}_{arch.arch_tag}_unsat_nonvacuous"
    run_thm = f"{cfg.stem}_{arch.arch_tag}_run_unsat"
    entry_label = f'Labels.label "{cfg.entry_fn}"'
    bound_expr = f"({compiled_name}.bound \"{cfg.entry_fn}\")"
    solve_name = f"solve_{arch.arch_tag}_of_fnspec"
    nv_wlen = "m6NvWorkLen" if cfg.abi_common else f"{cfg.stem}NvWorkLen"
    nv_pay = "m6NvPayload" if cfg.abi_common else f"{cfg.stem}NvPayload"

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
    unsat_ret = [
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
        f"      ⟨s, {entry_label}⟩",
    ]

    unsat_lam = (
        "        (fun _ _ hdom hu _ _ hm' =>"
        if cfg.solve_spec_has_sat
        else "        (fun _ _ hdom hu _ hm' =>"
    )
    nv_lam = (
        "        (fun _ _ _ _ _ htr _ =>"
        if cfg.solve_spec_has_sat
        else "        (fun _ _ _ _ htr _ =>"
    )
    run_lam = (
        "      (fun _ m' _ _ _ htr hm' =>"
        if cfg.solve_spec_has_sat
        else "      (fun _ m' _ _ htr hm' =>"
    )
    nv_ret = [
        "    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) "
        "(wlen : Nat)",
        "      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),",
        "      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧",
        "      work_ptr.toNat + wlen < 2 ^ 64 ∧",
        *arch.nv_reg_preds(bound_expr),
        "      Eventually (step1 Host.exe)",
        f"        (fun st => st.pc = ra ∧ {arch.ret_reg} = 20#64 ∧",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat)",
        f"        ⟨s, {entry_label}⟩",
    ]
    run_ret = [
        f"    Eventually ({arch.targ}.mach.step {compiled_name}.host)",
        "      (fun st =>",
        f"        {arch.targ}.mach.pc st = {arch.init_name}.ra0 ∧",
        f"        {arch.ret_gpr_expr} = 20#64 ∧",
        f"        ({arch.targ}.mach.mem ({arch.targ}.mach.data st) =⋆",
        "          (fun m' => nvM6UnsatCnf.Unsat ∧",
        "            (bytes nvM6CnfPtr nvM6UnsatBytes ⋆",
        f"              region nvM6UnsatWorkPtr {nv_wlen} ⋆ emp) m') ⋆",
        f"          {arch.targ}.Exit {arch.init_name}.sp0",
        f"            ({compiled_name}.bound \"{cfg.entry_fn}\") ⋆ emp))",
        f"      ({arch.targ}.mach.mkState",
        f"        ({arch.init_name}.initState (as := [i64, i64, i64, i64, i64])",
        f"          ({compiled_name}.bound \"{cfg.entry_fn}\")",
        f"          ({nv_pay} nvM6UnsatBytes)",
        "          (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,",
        f"            nvM6UnsatWorkPtr, BitVec.ofNat 64 {nv_wlen}, 16#64, ()))",
        f"        ({arch.targ}.mach.labelAddr {compiled_name}.host "
        f"\"{cfg.entry_fn}\"))",
    ]
    solve_iff = cfg.solve_bytes_suffix
    if cfg.abi_common:
        pkg_nm = unsat_pkg or f"{cfg.stem}UnsatPkg"
        nv_pkg_nm = nv_unsat_pkg or pkg_nm
        abi_args = (
            "⟨hrdi, hrsi, hrdx, hrcx, hr8⟩ hsp"
            if arch.key == "amd64"
            else "⟨hx0, hx1, hx2, hx3, hx4⟩ ⟨hra, hsp⟩"
        )
        nv_exact = (
            "  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,\n"
            "    h0, h1, h2, h3, h4, hsp, hdm, hev⟩"
            if arch.key == "amd64"
            else "  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,\n"
            "    h0, h1, h2, h3, h4, hsp.1, hsp.2, hdm, hev⟩"
        )
        unsat_proof_lines = [
            "  refine eventually_weaken _ _ _ _",
            "    (fun _ ⟨hpc, hdom, hu', ⟨hcal, hsp'⟩, hst⟩ =>",
            "      ⟨hpc, hdom, hu', hcal, hsp', hst⟩)",
            *_wrap_lean_app(
                "    (Examples.Kissat.KissatCertCommon.solve_bytes_unsat_of_abi",
                [
                    arch.kissat_abi,
                    pkg_nm,
                    compiled_name,
                    cfg.legal_sig,
                    "hh",
                    "k₀",
                    "hc",
                    "hu",
                    "cnf_ptr",
                    "work_ptr",
                    "fuel",
                    "cnfBytes",
                    "wlen",
                    "hcfit",
                    "hwfit",
                    "s",
                    "ra",
                    "R",
                    abi_args,
                    "hmem)",
                ],
                indent="      ",
            ),
        ]
        correct_proof_lines = _wrap_lean_app(
            "  Examples.Kissat.KissatCertCommon.unsat_correct_of_abi",
            [
                arch.kissat_abi,
                pkg_nm,
                compiled_name,
                cfg.legal_sig,
                "hh",
                "k₀",
                "hc",
                "hu",
                "cnf_ptr",
                "work_ptr",
                "fuel",
                "cnfBytes",
                "wlen",
                "hcfit",
                "hwfit",
                "s",
                "ra",
                "R",
                abi_args,
                "hmem",
            ],
        )
        nv_prefix_helpers: list[str] = []
        unsat_head = [f"theorem {unsat_thm} :", *unsat_ret[:-1], f"{unsat_ret[-1]} := by"]
        sound_head = [f"theorem {sound_thm} :", *sound_ret[:-1], f"{sound_ret[-1]} :="]
    else:
        nv_prefix_helpers = _render_nv_payload_helpers(cfg.stem)
        unsat_head = [f"theorem {unsat_thm} :", *unsat_ret[:-1], f"{unsat_ret[-1]} := by"]
        unsat_proof_lines = [
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
            f"    {cfg.env}{solve_iff}",
            f"      ({cfg.solve_spec_intro} (R := emp) hcfit hwfit",
            "        (by rw [sep_emp]; exact hm_in)",
            unsat_lam,
            "          by rw [sep_emp] at hm'; exact ⟨hdom, hu, hm'⟩))",
            "  refine eventually_weaken _ _ _ _ ?_",
            f"    ({cfg.prefix}CertLink.{solve_name} hfn cnf_ptr _ "
            "work_ptr _ fuel",
            f"      hspec s ra R {arch.unsat_solve_call_hyps})",
            f"  rintro st ⟨hpc, {arch.unsat_rintro_cal}, {arch.unsat_rintro_sp}, "
            "m', ⟨hdom, hu', hm'⟩, hst⟩",
            "  rw [sep_assoc] at hst",
            "  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst",
            "  rw [← sep_assoc] at hst'",
            f"  exact ⟨hpc, hdom, hu', {arch.unsat_rintro_cal}, "
            f"{arch.unsat_rintro_sp}, hst'⟩",
        ]
        sound_head = [f"theorem {sound_thm} :", *sound_ret[:-1], f"{sound_ret[-1]} :="]
        correct_proof_lines = [
            "  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)",
            f"    ({unsat_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen "
            "hcfit hwfit",
            f"      s ra R {arch.solve_call_hyps})",
        ]

    lines = [
        *nv_prefix_helpers,
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
            f"/-- Unconditional end-to-end {arch.isa_title} UNSAT soundness + "
            f"framing for `{cfg.mod}` (`432`-word `FullM6Hdr`). -/"
        ),
        *unsat_head,
        *unsat_proof_lines,
        "",
        *wrap_comment_lines(
            f"/-- Answer-only {arch.isa_title} UNSAT soundness corollary for "
            f"`{cfg.mod}`. -/"
        ),
        *sound_head,
        *correct_proof_lines,
        "",
    ]

    audit_names: list[str] = []
    if worst_case_axiom_len(ns, unsat_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(unsat_thm)
    elif cfg.print_axioms and worst_case_axiom_len(ns, "ax_unsat") <= MAX_AXIOM_REPORT_LEN:
        lines.extend(
            [
                "theorem ax_unsat :",
                *unsat_ret[:-1],
                f"{unsat_ret[-1]} :=",
                f"  {unsat_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen "
                "hcfit hwfit",
                f"    s ra R {arch.solve_call_hyps}",
                "",
            ]
        )
        audit_names.append("ax_unsat")
    if worst_case_axiom_len(ns, sound_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(sound_thm)
    elif (
        cfg.print_axioms
        and worst_case_axiom_len(ns, "ax_unsat_sound") <= MAX_AXIOM_REPORT_LEN
    ):
        lines.extend(
            [
                "theorem ax_unsat_sound :",
                *sound_ret[:-1],
                f"{sound_ret[-1]} :=",
                f"  {sound_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen "
                "hcfit hwfit",
                f"    s ra R {arch.solve_call_hyps}",
                "",
            ]
        )
        audit_names.append("ax_unsat_sound")

    if cfg.abi_common:
        pkg_nm = unsat_pkg or f"{cfg.stem}UnsatPkg"
        nv_pkg_nm = nv_unsat_pkg or pkg_nm
        nv_exact = (
            "  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,\n"
            "    h0, h1, h2, h3, h4, hsp, hdm, hev⟩"
            if arch.key == "amd64"
            else "  exact ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,\n"
            "    h0, h1, h2, h3, h4, hsp.1, hsp.2, hdm, hev⟩"
        )
        nv_body_lines = [
            f"theorem {nv_thm} [hh : Host] (k₀ : Nat)",
            f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
            "    (hu : Host.LabelsUnique) :",
            *nv_ret[:-1],
            f"{nv_ret[-1]} := by",
            "  obtain ⟨cp, wp, fu, cb, wl, s, ra, R, hcf, hwf,",
            "    ⟨h0, h1, h2, h3, h4⟩, hsp, hdm, hev⟩ :=",
            *_wrap_lean_app(
                "    Examples.Kissat.KissatCertCommon.unsat_nonvacuous_of_abi",
                [arch.kissat_abi, nv_pkg_nm, compiled_name, cfg.legal_sig, "hh", "k₀", "hc", "hu"],
                indent="      ",
            ),
            *nv_exact.splitlines(),
            "",
        ]
        run_body_lines = [
            f"theorem {run_thm} :",
            *run_ret[:-1],
            f"{run_ret[-1]} :=",
            *_wrap_lean_app(
                "  Examples.Kissat.KissatCertCommon.run_unsat_of_abi",
                [arch.kissat_abi, nv_pkg_nm, compiled_name, cfg.legal_sig],
            ),
            "",
        ]
    else:
        nv_body_lines = [
            f"theorem {nv_thm} [hh : Host] (k₀ : Nat)",
            f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
            "    (hu : Host.LabelsUnique) :",
            *nv_ret[:-1],
            f"{nv_ret[-1]} := by",
            f"  have hfn : {arch.targ}.FnSpec hh \"{cfg.entry_fn}\"",
            f"      ({cfg.unsat_env} \"{cfg.entry_fn}\" "
            "[i64, i64, i64, i64, i64] [i64])",
            f"      ({compiled_name}.bound \"{cfg.entry_fn}\") 0 :=",
            f"    ({cfg.prefix}CertLink.mk_module_fnspec {cfg.unsat_env} "
            f"{cfg.unsat_module_ok}",
            f"      (fun g _ => {cfg.unsat_no_exit} g.name g.as g.rs) k₀ hc hu "
            f"solve_in_{cfg.mod}).2",
            f"  let b := {compiled_name}.bound \"{cfg.entry_fn}\"",
            f"  let bs := {nv_pay} nvM6UnsatBytes",
            f"  let s := {arch.init_name}.initState "
            "(as := [i64, i64, i64, i64, i64]) b bs",
            "    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,",
            f"      nvM6UnsatWorkPtr, BitVec.ofNat 64 {nv_wlen}, 16#64, ())",
            *arch.sat_nv_init_proof(
                compiled_name, "nvM6UnsatBytes", "nvM6UnsatWorkPtr", nv_wlen, nv_pay
            ),
            f"  refine ⟨nvM6CnfPtr, nvM6UnsatWorkPtr, 16#64, nvM6UnsatBytes, "
            f"{nv_wlen},",
            "    s, 0x1234, emp, by decide, by decide, rfl, rfl, rfl, rfl, rfl,",
            *([] if arch.key == "amd64" else ["    rfl,"]),
            "    hhsp, hdm, ?_⟩",
            f"  have hspec : {cfg.unsat_env} \"{cfg.entry_fn}\" "
            "[i64, i64, i64, i64, i64] [i64]",
            "      (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,",
            f"        nvM6UnsatWorkPtr, BitVec.ofNat 64 {nv_wlen}, 16#64, ())",
            "      (bs.At 0x1000#64) (fun r _ => r.fst = 20#64 ∧ nvM6UnsatCnf.Unsat)",
            "      (fun _ _ _ _ => False) :=",
            f"    {cfg.unsat_env}{solve_iff}",
            f"      ({cfg.solve_spec_intro} (R := emp) "
            "(by decide) (by decide)",
            "        (by",
            f"          rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]",
            f"          exact {nv_pay}_sep nvM6UnsatBytes (by decide))",
            nv_lam,
            f"          ⟨htr 1 2 9 (by decide) (by decide) (by decide) "
            f"{cfg.stem}Nv_unsat_bound",
            "            (by decide) nvM6Unsat_header nvM6Unsat_unitTrace, "
            "nvM6UnsatCnf_unsat⟩))",
            f"  have hev := {cfg.prefix}CertLink.{solve_name} hfn nvM6CnfPtr _",
            "    nvM6UnsatWorkPtr _ 16#64 hspec s 0x1234 emp",
            "    rfl rfl rfl rfl rfl"
            + ("" if arch.key == "amd64" else " rfl")
            + " hhsp h1'",
            "  exact eventually_weaken _ _ _ _",
            "    (fun _ ⟨hpc, _, _, _, ⟨h20, huns⟩, _⟩ =>",
            "      ⟨hpc, h20, nvM6UnsatCnf, parseDimacs_nvM6UnsatBytes, huns⟩)",
            "    hev",
            "",
        ]
        run_body_lines = [
            f"theorem {run_thm} :",
            *run_ret[:-1],
            f"{run_ret[-1]} := by",
            f"  refine {compiled_name}.eventually_ret1_sep_i64_of_legalSigAll_optInlinePolicy",
            f"    {arch.init_name}",
            f"    {cfg.unsat_env} {cfg.unsat_module_ok} {cfg.legal_sig} "
            f"solve_in_{cfg.mod} rfl",
            f"    ({cfg.unsat_no_exit} \"{cfg.entry_fn}\" "
            "[i64, i64, i64, i64, i64] [i64])",
            f"    ({nv_pay} nvM6UnsatBytes)",
            "    (nvM6CnfPtr, BitVec.ofNat 64 nvM6UnsatBytes.length,",
            f"      nvM6UnsatWorkPtr, BitVec.ofNat 64 {nv_wlen}, 16#64, ())",
            "    20#64",
            "    (fun m' => nvM6UnsatCnf.Unsat ∧",
            "      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆",
            f"        region nvM6UnsatWorkPtr {nv_wlen} ⋆ emp) m')",
            f"    (by rw [{nv_pay}_length]; unfold {nv_wlen}; decide) rfl",
            "    (Q := fun r m' => r = (20#64, ()) ∧ nvM6UnsatCnf.Unsat ∧",
            "      (bytes nvM6CnfPtr nvM6UnsatBytes ⋆",
            f"        region nvM6UnsatWorkPtr {nv_wlen} ⋆ emp) m')",
            "    ?_ (fun _ _ h => h) (by decide)",
            f"  exact {cfg.unsat_env}{solve_iff}",
            f"    ({cfg.solve_spec_intro} (R := emp) "
            "(by decide) (by decide)",
            "      (by",
            f"        rw [sep_emp, nvM6UnsatWorkPtr_eq_fullNvWorkPtr]",
            f"        exact {nv_pay}_sep nvM6UnsatBytes (by decide))",
            run_lam,
            f"        ⟨congrArg (·, ()) (htr 1 2 9 (by decide) (by decide) (by decide) "
            f"{cfg.stem}Nv_unsat_bound",
            "          (by decide) nvM6Unsat_header nvM6Unsat_unitTrace),",
            "         nvM6UnsatCnf_unsat, hm'⟩))",
            "",
        ]

    lines.extend(
        [
            "end Unsat",
            "",
            *wrap_comment_lines(
                f"/-- Unconditional concrete {arch.isa_title} UNSAT non-vacuity for "
                f"`{cfg.mod}` on `432`-word `FullM6Hdr` (`nvM6UnsatBytes`, "
                f"`{M6_NV_WORK_LEN}`-byte workspace, `fuel = 16`). -/"
            ),
            *nv_body_lines,
            *wrap_comment_lines(
                f"/-- Closed concrete-host {arch.isa_title} UNSAT execution witness "
                f"on `{compiled_name}.host` (`432`-word `FullM6Hdr`). -/"
            ),
            *run_body_lines,
        ]
    )

    if worst_case_axiom_len(ns, nv_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(nv_thm)
    elif cfg.print_axioms and worst_case_axiom_len(ns, "ax_unsat_nv") <= MAX_AXIOM_REPORT_LEN:
        lines.extend(
            [
                "theorem ax_unsat_nv [hh : Host] (k₀ : Nat)",
                f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
                "    (hu : Host.LabelsUnique) :",
                *nv_ret[:-1],
                f"{nv_ret[-1]} :=",
                f"  {nv_thm} k₀ hc hu",
                "",
            ]
        )
        audit_names.append("ax_unsat_nv")
    if worst_case_axiom_len(ns, run_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(run_thm)
    elif cfg.print_axioms and worst_case_axiom_len(ns, "ax_run_unsat") <= MAX_AXIOM_REPORT_LEN:
        lines.extend(
            [
                "theorem ax_run_unsat :",
                *run_ret[:-1],
                f"{run_ret[-1]} :=",
                f"  {run_thm}",
                "",
            ]
        )
        audit_names.append("ax_run_unsat")
    return lines, audit_names


def render_sound_wrapper(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>Sound.lean` with SAT+UNSAT (`readModelFromWorkM6`) & SAT non-vacuity."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}Sound"
    top_mod = f"{arch.ns_prefix}.{cfg.prefix}"
    link_mod = f"{arch.ns_prefix}.{cfg.prefix}CertLink"
    compiled_name = f"{cfg.camel_prefix}_compiled_{arch.arch_tag}"
    entry_label = f'Labels.label "{cfg.entry_fn}"'
    bound_expr = f"({compiled_name}.bound \"{cfg.entry_fn}\")"
    solve_name = f"solve_{arch.arch_tag}_of_fnspec"
    nv_wlen = f"{cfg.stem}SoundNvWorkLen"
    nv_pay = f"{cfg.stem}SoundNvPayload"

    sound_fnspec = f"{cfg.stem}_sound_module_fnspec"
    model_thm = f"{cfg.stem}_solve_bytes_model_{arch.arch_tag}"
    sat_sound_thm = f"{cfg.stem}_solve_bytes_sound_{arch.arch_tag}"
    model_only_thm = f"{cfg.stem}_solve_bytes_model_only_{arch.arch_tag}"
    sound_only_thm = f"{cfg.stem}_solve_bytes_sound_only_{arch.arch_tag}"
    sat_nv_thm = f"{cfg.stem}_{arch.arch_tag}_sat_nonvacuous"
    run_sat_thm = f"{cfg.stem}_{arch.arch_tag}_run_sat"

    sat_sound_mod = cfg.sat_sound_mod or "LeanQbe.T.Examples.Kissat.FullM6SatSound"
    sat_nv_mod = cfg.sat_nv_mod or "LeanQbe.T.Examples.Kissat.FullM6SatNv"

    model_sig = [
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        f"        ({arch.ret_reg} = 0#64 ∨",
        f"          {arch.ret_reg} = 10#64 ∨",
        f"          {arch.ret_reg} = 20#64) ∧",
        f"        ({arch.ret_reg} = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
        f"        ({arch.ret_reg} = 10#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧",
        "            cnf.Sat (readModelFromWorkM6 st.data.dmem work_ptr)) ∧",
        *arch.callee_saved_pred,
        f"        {arch.sp_ret} ∧",
        *arch.unsat_st_dmem(bound_expr),
        f"      ⟨s, {entry_label}⟩",
    ]
    sound_sig = [
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        f"        ({arch.ret_reg} = 0#64 ∨",
        f"          {arch.ret_reg} = 10#64 ∨",
        f"          {arch.ret_reg} = 20#64) ∧",
        f"        ({arch.ret_reg} = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
        f"        ({arch.ret_reg} = 10#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧",
        "            ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α) ∧",
        *arch.callee_saved_pred,
        f"        {arch.sp_ret} ∧",
        *arch.unsat_st_dmem(bound_expr),
        f"      ⟨s, {entry_label}⟩",
    ]
    model_only_sig = [
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        f"        ({arch.ret_reg} = 0#64 ∨",
        f"          {arch.ret_reg} = 10#64 ∨",
        f"          {arch.ret_reg} = 20#64) ∧",
        f"        ({arch.ret_reg} = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
        f"        ({arch.ret_reg} = 10#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧",
        "            cnf.Sat (readModelFromWorkM6 st.data.dmem work_ptr)))",
        f"      ⟨s, {entry_label}⟩",
    ]
    sound_only_sig = [
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        f"        ({arch.ret_reg} = 0#64 ∨",
        f"          {arch.ret_reg} = 10#64 ∨",
        f"          {arch.ret_reg} = 20#64) ∧",
        f"        ({arch.ret_reg} = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
        f"        ({arch.ret_reg} = 10#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧",
        "            ¬ cnf.Unsat ∧ ∃ α, cnf.Sat α))",
        f"      ⟨s, {entry_label}⟩",
    ]

    sat_nv_lines = [
        f"private def {nv_wlen} : Nat := {M6_NV_WORK_LEN}",
        "",
        f"private def {nv_pay} (cnfBytes : List UInt8) : List UInt8 :=",
        f"  cnfBytes ++ List.replicate {nv_wlen} 0",
        "",
        f"private theorem {nv_pay}_length (cnfBytes : List UInt8) :",
        f"    ({nv_pay} cnfBytes).length = cnfBytes.length + {nv_wlen} := by",
        f"  simp only [{nv_pay}, List.length_append, List.length_replicate]",
        "",
        f"private theorem {nv_pay}_sep (cnfBytes : List UInt8) "
        "(hcb : cnfBytes.length ≤ 2048) :",
        f"    (bytes nvM6CnfPtr cnfBytes ⋆ region (fullNvWorkPtr cnfBytes) {nv_wlen})",
        f"      (({nv_pay} cnfBytes).At nvM6CnfPtr) :=",
        "  nv_sep_append rfl",
        f"    (by unfold {nv_wlen}; rw [List.length_replicate]; omega)",
        f"    rfl ⟨List.replicate {nv_wlen} 0, List.length_replicate, rfl⟩",
        "",
    ]

    # Alias short names when full name exceeds 114c `#print axioms` bound.
    audit_names: list[str] = []
    alias_defs: list[str] = []

    if worst_case_axiom_len(ns, sound_fnspec) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(sound_fnspec)
    elif cfg.print_axioms and worst_case_axiom_len(ns, "ax_sound_fnspec") <= MAX_AXIOM_REPORT_LEN:
        alias_defs.extend(
            [
                "theorem ax_sound_fnspec [hh : Host] (k₀ : Nat)",
                f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
                "    (hu : Host.LabelsUnique)",
                f"    {{f : Fn}} (hf : f ∈ {cfg.mod}.fns) :",
                f"    {arch.targ}.Defined hh f.name ∧",
                f"      {arch.targ}.FnSpec hh f.name ({cfg.sound_env} f.name f.as f.rs)",
                f"        ({compiled_name}.bound f.name) 0 :=",
                f"  {sound_fnspec} k₀ hc hu hf",
                "",
            ]
        )
        audit_names.append("ax_sound_fnspec")

    if worst_case_axiom_len(ns, model_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(model_thm)
    elif cfg.print_axioms and worst_case_axiom_len(ns, "ax_model") <= MAX_AXIOM_REPORT_LEN:
        alias_defs.extend(
            [
                "section Axioms",
                "variable [hh : Host] (k₀ : Nat)",
                f"  (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
                "  (hu : Host.LabelsUnique)",
                "  (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)",
                "  (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)",
                "  (hwfit : work_ptr.toNat + wlen < 2 ^ 64)",
                "  (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)",
                *arch.unsat_reg_hyps(bound_expr),
                "include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R",
                f"  {arch.solve_call_hyps}",
                "",
                "theorem ax_model :",
                *model_only_sig[:-1],
                f"{model_only_sig[-1]} :=",
                f"  {model_only_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit",
                f"    s ra R {arch.solve_call_hyps}",
                "",
                "theorem ax_sound :",
                *sound_only_sig[:-1],
                f"{sound_only_sig[-1]} :=",
                f"  {sound_only_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit",
                f"    s ra R {arch.solve_call_hyps}",
                "",
                "end Axioms",
                "",
            ]
        )
        audit_names.extend(["ax_model", "ax_sound"])

    sat_nv_stmt = [
        "    ∃ (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)",
        "      (s : MachineData) (ra : Int64) (R : Mem 64 → Prop),",
        "      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧",
        "      work_ptr.toNat + wlen < 2 ^ 64 ∧",
        *arch.nv_reg_preds(bound_expr),
        "      Eventually (step1 Host.exe)",
        "        (fun st => st.pc = ra ∧",
        f"          ({arch.ret_reg} = 0#64 ∨",
        f"            {arch.ret_reg} = 10#64) ∧",
        f"          {arch.ret_reg} ≠ 20#64 ∧",
        f"          ({arch.ret_reg} = 10#64 →",
        "            ¬ nvM6SatCnf.Unsat ∧",
        "            nvM6SatCnf.Sat (readModelFromWorkM6 st.data.dmem work_ptr)))",
        f"        ⟨s, {entry_label}⟩",
    ]
    if worst_case_axiom_len(ns, sat_nv_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(sat_nv_thm)
    elif cfg.print_axioms and worst_case_axiom_len(ns, "ax_sat_nv") <= MAX_AXIOM_REPORT_LEN:
        alias_defs.extend(
            [
                "theorem ax_sat_nv [hh : Host] (k₀ : Nat)",
                f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
                "    (hu : Host.LabelsUnique) :",
                *sat_nv_stmt[:-1],
                f"{sat_nv_stmt[-1]} :=",
                f"  {sat_nv_thm} k₀ hc hu",
                "",
            ]
        )
        audit_names.append("ax_sat_nv")

    if worst_case_axiom_len(ns, run_sat_thm) <= MAX_AXIOM_REPORT_LEN:
        audit_names.append(run_sat_thm)

    axiom_section = (
        [*render_axiom_prints(ns, audit_names), ""]
        if (cfg.print_axioms and audit_names)
        else []
    )

    lines = [
        "module",
        "",
        f"public import {top_mod}",
        f"public import {sat_sound_mod}",
        f"import {arch.lemmas_mod}",
        "import LeanQbe.T.Logic.MemLemmas",
        "import Std.Sat.CNF.Basic",
        "import Kraken.Mem",
        "import Kraken.Separation",
        "",
        "/-!",
        f"# {cfg.prefix} (`{cfg.total_fns}` fns) {arch.isa_title} UNSAT + SAT Soundness",
        "",
        *wrap_comment_lines(
            f"Additive dual-soundness and concrete SAT non-vacuity layer over "
            f"`{top_mod}.{compiled_name}` and `readModelFromWorkM6` (`432`-word "
            "`FullM6Hdr`, zero opposite-architecture imports)."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "public section",
        "",
        f"namespace {ns}",
        "",
        *wrap_open_pairs(
            list(
                dict.fromkeys(
                    [
                        "Std",
                        "Std.Sat",
                        "Std.ExtHashMap",
                        "LeanQbe.T",
                        "LeanQbe.T.Examples.Kissat",
                        "LeanQbe.T.Examples.Kissat.Full",
                        "LeanQbe.T.Examples.Kissat.FullM6",
                        "LeanQbe.T.Examples.Kissat.FullM6Hdr",
                        "LeanQbe.T.Examples.LratBytes",
                        cfg.source_mod,
                        arch.ns_prefix,
                        link_mod,
                        top_mod,
                        "Kraken",
                    ]
                )
            )
        ),
        "",
        *wrap_comment_lines(
            f"/-- Unconditional whole-module `Defined` + `FnSpec` for all "
            f"`{cfg.total_fns}` functions in `{cfg.mod}` under `{cfg.sound_env}` "
            f"on {arch.isa_title}. -/"
        ),
        f"theorem {sound_fnspec} [hh : Host] (k₀ : Nat)",
        f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
        "    (hu : Host.LabelsUnique)",
        f"    {{f : Fn}} (hf : f ∈ {cfg.mod}.fns) :",
        f"    {arch.targ}.Defined hh f.name ∧",
        f"      {arch.targ}.FnSpec hh f.name ({cfg.sound_env} f.name f.as f.rs)",
        f"        ({compiled_name}.bound f.name) 0 :=",
        f"  {cfg.prefix}CertLink.mk_module_fnspec {cfg.sound_env} {cfg.sound_module_ok}",
        f"    (fun g _ => {cfg.sound_no_exit} g.name g.as g.rs) k₀ hc hu hf",
        "",
        f"private theorem solve_in_{cfg.mod} :",
        f"    {cfg.entry_const} ∈ {cfg.mod}.fns := by",
        "  exact List.mem_of_getElem?",
        f"    (by t_kernel_rfl : ({cfg.mod}.fns)[{cfg.entry_idx}]? = "
        f"some {cfg.entry_const})",
        "",
        "private theorem sep_exists_eq {P Q : Mem 64 → Prop} {M : Mem 64}",
        "    (h : (P ⋆ Q) M) : ∃ m : Mem 64, P m ∧ (Eq m ⋆ Q) M := by",
        "  have hm := sep_mono (Q := Q)",
        "    (fun x hx => (⟨x, ⟨hx, rfl⟩⟩ : ∃ m : Mem 64, P m ∧ Eq m x)) h",
        "  rw [sep_ex_l] at hm",
        "  obtain ⟨m, hm'⟩ := hm",
        "  exact ⟨m, sep_pure_l (φ := P m) (P := Eq m) (R := Q).mp hm'⟩",
        "",
        *sat_nv_lines,
        "section Sound",
        "",
        "variable [hh : Host] (k₀ : Nat)",
        f"  (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
        "  (hu : Host.LabelsUnique)",
        "  (cnf_ptr work_ptr fuel : BitVec 64) (cnfBytes : List UInt8) (wlen : Nat)",
        "  (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)",
        "  (hwfit : work_ptr.toNat + wlen < 2 ^ 64)",
        "  (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)",
        *arch.unsat_reg_hyps(bound_expr),
        "include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit s ra R",
        f"  {arch.solve_call_hyps}",
        "",
        *wrap_comment_lines(
            f"/-- Unconditional end-to-end {arch.isa_title} UNSAT + constructive "
            f"`readModelFromWorkM6` SAT model soundness for `{cfg.mod}` with framing. -/"
        ),
        f"theorem {model_thm} :",
        *model_sig[:-1],
        f"{model_sig[-1]} := by",
        f"  have hfn := ({sound_fnspec} k₀ hc hu solve_in_{cfg.mod}).2",
        *arch.unsat_hm0(bound_expr),
        "    rw [← sep_assoc]; exact hmem",
        "  obtain ⟨m, hm_in, hm_dmem⟩ := sep_exists_eq hm0",
        *arch.unsat_hm_dmem(bound_expr),
        "    rw [sep_assoc]; exact hm_dmem",
        f"  have hspec : {cfg.sound_env} \"{cfg.entry_fn}\" "
        "[i64, i64, i64, i64, i64] [i64]",
        "      (cnf_ptr, BitVec.ofNat 64 cnfBytes.length, work_ptr,",
        "        BitVec.ofNat 64 wlen, fuel, ()) m",
        "      (fun r m' =>",
        "        (r.fst = 0#64 ∨ r.fst = 10#64 ∨ r.fst = 20#64) ∧",
        "        (r.fst = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
        "        (r.fst = 10#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧",
        "          ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →",
        "            cnf.Sat (readModelFromWorkM6 M work_ptr)) ∧",
        "        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen) m')",
        "      (fun _ _ _ _ => False) :=",
        f"    {cfg.sound_env}_solve_bytes",
        "      (fullM6SolveBytesCoreModelSpec_intro (R := emp) hcfit hwfit",
        "        (by rw [sep_emp]; exact hm_in)",
        "        (fun _ _ hdom hu hmod _ hm' =>",
        "          by rw [sep_emp] at hm'; exact ⟨hdom, hu, hmod, hm'⟩))",
        "  refine eventually_weaken _ _ _ _ ?_",
        f"    ({cfg.prefix}CertLink.{solve_name} hfn cnf_ptr _ work_ptr _ fuel",
        f"      hspec s ra R {arch.unsat_solve_call_hyps})",
        f"  rintro st ⟨hpc, {arch.unsat_rintro_cal}, {arch.unsat_rintro_sp}, "
        "m', ⟨hdom, hu', hmod, hm'⟩, hst⟩",
        "  have hst_frame : (Eq m' ⋆",
        *(
            [
                "      (region (s.regs.get64 .rsp - BitVec.ofNat 64",
                f"          {bound_expr})",
                f"        ({bound_expr} + 8) ⋆ R)) st.data.dmem := by",
            ]
            if arch.key == "amd64"
            else [
                "      (region (s.regs.SP.toBitVec - BitVec.ofNat 64",
                f"          {bound_expr})",
                f"        {bound_expr} ⋆ R)) st.data.dmem := by",
            ]
        ),
        "    rw [← sep_assoc]; exact hst",
        f"  have hsat_st : {arch.ret_reg} = 10#64 →",
        "      ∃ cnf, parseDimacs cnfBytes = some cnf ∧",
        "        cnf.Sat (readModelFromWorkM6 st.data.dmem work_ptr) := by",
        "    intro h10",
        "    obtain ⟨cnf, hparse, hf⟩ := hmod h10",
        "    exact ⟨cnf, hparse, hf _ st.data.dmem hst_frame⟩",
        "  rw [sep_assoc] at hst",
        "  have hst' := sep_mono (fun _ heq => heq ▸ hm') hst",
        "  rw [← sep_assoc] at hst'",
        f"  exact ⟨hpc, hdom, hu', hsat_st, {arch.unsat_rintro_cal}, "
        f"{arch.unsat_rintro_sp}, hst'⟩",
        "",
        *wrap_comment_lines(
            f"/-- Unconditional {arch.isa_title} UNSAT + existential SAT soundness "
            f"for `{cfg.mod}` with exact framing. -/"
        ),
        f"theorem {sat_sound_thm} :",
        *sound_sig[:-1],
        f"{sound_sig[-1]} := by",
        "  refine eventually_weaken _ _ _ _",
        f"    (fun _ ⟨hpc, hdom, hu', hmod, {arch.unsat_rintro_cal}, "
        f"{arch.unsat_rintro_sp}, hmem'⟩ =>",
        "      ⟨hpc, hdom, hu', fun h10 =>",
        "        let ⟨cnf, hp, hsat⟩ := hmod h10",
        "        ⟨cnf, hp, cnf_not_unsat_of_sat hsat⟩,",
        f"        {arch.unsat_rintro_cal}, {arch.unsat_rintro_sp}, hmem'⟩)",
        f"    ({model_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit",
        f"      s ra R {arch.solve_call_hyps})",
        "",
        *wrap_comment_lines(
            f"/-- Answer-only {arch.isa_title} UNSAT + `readModelFromWorkM6` SAT "
            f"model soundness corollary for `{cfg.mod}`. -/"
        ),
        f"theorem {model_only_thm} :",
        *model_only_sig[:-1],
        f"{model_only_sig[-1]} :=",
        "  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)",
        f"    ({model_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit",
        f"      s ra R {arch.solve_call_hyps})",
        "",
        *wrap_comment_lines(
            f"/-- Answer-only {arch.isa_title} UNSAT + existential SAT soundness "
            f"corollary for `{cfg.mod}`. -/"
        ),
        f"theorem {sound_only_thm} :",
        *sound_only_sig[:-1],
        f"{sound_only_sig[-1]} :=",
        "  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)",
        f"    ({sat_sound_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit",
        f"      s ra R {arch.solve_call_hyps})",
        "",
        "end Sound",
        "",
        *wrap_comment_lines(
            f"/-- Unconditional concrete {arch.isa_title} SAT non-vacuity for "
            f"`{cfg.mod}` on `432`-word `FullM6Hdr` (`nvM6SatBytes`, "
            f"`{M6_NV_WORK_LEN}`-byte workspace, `fuel = 16`). -/"
        ),
        f"theorem {sat_nv_thm} [hh : Host] (k₀ : Nat)",
        f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
        "    (hu : Host.LabelsUnique) :",
        *sat_nv_stmt[:-1],
        f"{sat_nv_stmt[-1]} := by",
        f"  have hfn := ({sound_fnspec} k₀ hc hu solve_in_{cfg.mod}).2",
        f"  let b := {compiled_name}.bound \"{cfg.entry_fn}\"",
        f"  let bs := {nv_pay} nvM6SatBytes",
        f"  let s := {arch.init_name}.initState "
        "(as := [i64, i64, i64, i64, i64]) b bs",
        "    (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,",
        f"      nvM6SatWorkPtr, BitVec.ofNat 64 {nv_wlen}, 16#64, ())",
        *(
            [
                f"  have h1 := x64InitMem_entry b 0x1234 bs ({compiled_name}.bound_le_max _)",
                f"    (by rw [{nv_pay}_length]; unfold {nv_wlen}; decide)",
                "  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ x64Target.Entry 0x0ff8#64 0x1234 b ⋆ emp at h1",
                "  dsimp only [Target.Entry, x64Target, x64FrameTarget, x64FramePreds] at h1",
                "  have h1' : (Eq (bs.At 0x1000#64) ⋆",
                "      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆",
                "        cell64 (s.regs.get64 .rsp) (0x1234 : Int64).toBitVec) ⋆ emp) s.dmem := by",
                "    rw [show s.regs.get64 .rsp = 0x0ff8#64 from rfl]; exact h1",
                f"  have hdm : (bytes nvM6CnfPtr nvM6SatBytes ⋆",
                f"      region nvM6SatWorkPtr {nv_wlen} ⋆",
                "      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆",
                "        cell64 (s.regs.get64 .rsp) (0x1234 : Int64).toBitVec) ⋆ emp) s.dmem := by",
                "    refine sep_mono (Q := emp)",
                "      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))",
                f"        (fun _ heq => heq ▸ by",
                f"          rw [nvM6SatWorkPtr_eq_fullNvWorkPtr]",
                f"          exact {nv_pay}_sep nvM6SatBytes (by unfold nvM6SatBytes; decide))) h1'",
                "  have hhsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0 := by",
                "    rw [show s.regs.get64 .rsp = 0x0ff8#64 from rfl]; decide",
            ]
            if arch.key == "amd64"
            else [
                f"  have h1 := armInitMem_entry b bs ({compiled_name}.bound_le_max _)",
                f"    (by rw [{nv_pay}_length]; unfold {nv_wlen}; decide)",
                "  change s.dmem =⋆ Eq (bs.At 0x1000#64) ⋆ armTarget.Entry 0x1000#64 0x1234 b ⋆ emp at h1",
                "  dsimp only [Target.Entry, armTarget, armFrameTarget, armFramePreds] at h1",
                "  simp only [region_zero, sep_emp] at h1",
                "  have h1' : (Eq (bs.At 0x1000#64) ⋆",
                "      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem := by",
                "    rw [show s.regs.SP.toBitVec = 0x1000#64 from rfl]; simpa [sep_emp] using h1",
                f"  have hdm : (bytes nvM6CnfPtr nvM6SatBytes ⋆",
                f"      region nvM6SatWorkPtr {nv_wlen} ⋆",
                "      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp) s.dmem :=",
                "    sep_mono (Q := emp)",
                "      (fun _ => sep_mono (P := Eq (bs.At 0x1000#64))",
                f"        (fun _ heq => heq ▸ by",
                f"          rw [nvM6SatWorkPtr_eq_fullNvWorkPtr]",
                f"          exact {nv_pay}_sep nvM6SatBytes (by unfold nvM6SatBytes; decide))) h1'",
                "  have hhsp : s.regs.SP.toNat % 16 = 0 := by rw [show s.regs.SP = 4096 from rfl]; decide",
            ]
        ),
        f"  refine ⟨nvM6CnfPtr, nvM6SatWorkPtr, 16#64, nvM6SatBytes, {nv_wlen},",
        "    s, 0x1234, emp, by decide, by decide, rfl, rfl, rfl, rfl, rfl,",
        *([] if arch.key == "amd64" else ["    rfl,"]),
        "    hhsp, hdm, ?_⟩",
        f"  have hspec : {cfg.sound_env} \"{cfg.entry_fn}\" "
        "[i64, i64, i64, i64, i64] [i64]",
        "      (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,",
        f"        nvM6SatWorkPtr, BitVec.ofNat 64 {nv_wlen}, 16#64, ())",
        "      (bs.At 0x1000#64)",
        "      (fun r m' =>",
        "        (r.fst = 0#64 ∨ r.fst = 10#64) ∧ r.fst ≠ 20#64 ∧",
        "        (r.fst = 10#64 →",
        "          ¬ nvM6SatCnf.Unsat ∧",
        "          ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →",
        "            nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr)))",
        "      (fun _ _ _ _ => False) :=",
        f"    {cfg.sound_env}_solve_bytes",
        "      (fullM6SolveBytesCoreModelSpec_intro (R := emp) (by decide) (by decide)",
        "        (by",
        f"          rw [sep_emp, nvM6SatWorkPtr_eq_fullNvWorkPtr]",
        f"          exact {nv_pay}_sep nvM6SatBytes (by unfold nvM6SatBytes; decide))",
        "        (fun r m' hdom h20 h10 _ _ => by",
        "          have hne20 : r ≠ 20#64 := by",
        "            intro h20eq",
        "            obtain ⟨cnf, hp, hu⟩ := h20 h20eq",
        "            rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp",
        "            subst hp; exact nvM6SatCnf_not_unsat hu",
        "          have hdom' : r = 0#64 ∨ r = 10#64 := by",
        "            rcases hdom with rfl | rfl | rfl",
        "            · exact Or.inl rfl",
        "            · exact Or.inr rfl",
        "            · exact False.elim (hne20 rfl)",
        "          refine ⟨hdom', hne20, fun hr10 => ?_⟩",
        "          obtain ⟨cnf, hp, hsat⟩ := h10 hr10",
        "          rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp",
        "          subst hp; exact ⟨nvM6SatCnf_not_unsat, hsat⟩))",
        f"  have hev := {cfg.prefix}CertLink.{solve_name} hfn nvM6CnfPtr _",
        "    nvM6SatWorkPtr _ 16#64 hspec s 0x1234 emp",
        "    rfl rfl rfl rfl rfl"
        + ("" if arch.key == "amd64" else " rfl")
        + " hhsp h1'",
        "  refine eventually_weaken _ _ _ _ ?_ hev",
        f"  rintro st ⟨hpc, _, _, m', ⟨hdom', hne20, hsat⟩, hst⟩",
        "  refine ⟨hpc, hdom', hne20, fun h10 => ?_⟩",
        "  obtain ⟨hnu, hf⟩ := hsat h10",
        "  have hst_frame : (Eq m' ⋆",
        *(
            [
                "      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ emp)) "
                "st.data.dmem := by",
            ]
            if arch.key == "amd64"
            else [
                "      (region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ emp)) "
                "st.data.dmem := by",
            ]
        ),
        "    rw [← sep_assoc]; exact hst",
        "  exact ⟨hnu, hf _ st.data.dmem hst_frame⟩",
        "",
        *wrap_comment_lines(
            f"/-- Closed concrete-host {arch.isa_title} SAT non-vacuity witness on "
            f"`{compiled_name}.host` (`432`-word `FullM6Hdr`). -/"
        ),
        f"theorem {run_sat_thm} :",
        f"    Eventually ({arch.targ}.mach.step {compiled_name}.host)",
        "      (fun st =>",
        f"        {arch.targ}.mach.pc st = {arch.init_name}.ra0 ∧",
        f"        ({arch.ret_gpr_expr} = 0#64 ∨",
        f"          {arch.ret_gpr_expr} = 10#64) ∧",
        f"        {arch.ret_gpr_expr} ≠ 20#64 ∧",
        f"        ({arch.ret_gpr_expr} = 10#64 →",
        "          ¬ nvM6SatCnf.Unsat ∧",
        f"          nvM6SatCnf.Sat (readModelFromWorkM6",
        f"            ({arch.targ}.mach.mem ({arch.targ}.mach.data st)) nvM6SatWorkPtr)))",
        f"      ({arch.targ}.mach.mkState",
        f"        ({arch.init_name}.initState (as := [i64, i64, i64, i64, i64])",
        f"          ({compiled_name}.bound \"{cfg.entry_fn}\")",
        f"          ({nv_pay} nvM6SatBytes)",
        "          (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,",
        f"            nvM6SatWorkPtr, BitVec.ofNat 64 {nv_wlen}, 16#64, ()))",
        f"        ({arch.targ}.mach.labelAddr {compiled_name}.host "
        f"\"{cfg.entry_fn}\")) := by",
        f"  refine {compiled_name}.eventually_fnSpec_optInlinePolicy {arch.init_name}",
        f"    {cfg.sound_env} {cfg.sound_module_ok} solve_in_{cfg.mod}",
        f"    ({cfg.legal_sig} _ solve_in_{cfg.mod}).1 "
        f"({cfg.legal_sig} _ solve_in_{cfg.mod}).2",
        f"    ({cfg.sound_no_exit} \"{cfg.entry_fn}\" "
        "[i64, i64, i64, i64, i64] [i64])",
        f"    ({nv_pay} nvM6SatBytes)",
        "    (nvM6CnfPtr, BitVec.ofNat 64 nvM6SatBytes.length,",
        f"      nvM6SatWorkPtr, BitVec.ofNat 64 {nv_wlen}, 16#64, ())",
        f"    (by rw [{nv_pay}_length]; unfold {nv_wlen}; decide) rfl",
        "    (Q := fun rs m' =>",
        "      (rs.fst = 0#64 ∨ rs.fst = 10#64) ∧ rs.fst ≠ 20#64 ∧",
        "      (rs.fst = 10#64 →",
        "        ¬ nvM6SatCnf.Unsat ∧",
        "        ∀ (F : Mem 64 → Prop) (M : Mem 64), (Eq m' ⋆ F) M →",
        "          nvM6SatCnf.Sat (readModelFromWorkM6 M nvM6SatWorkPtr)))",
        "    ?_ ?_ (by decide)",
        f"  · exact {cfg.sound_env}_solve_bytes",
        "      (fullM6SolveBytesCoreModelSpec_intro (R := emp) (by decide) (by decide)",
        "        (by",
        f"          rw [sep_emp, nvM6SatWorkPtr_eq_fullNvWorkPtr]",
        f"          exact {nv_pay}_sep nvM6SatBytes (by unfold nvM6SatBytes; decide))",
        "        (fun r m' hdom h20 h10 _ _ => by",
        "          have hne20 : r ≠ 20#64 := by",
        "            intro h20eq",
        "            obtain ⟨cnf, hp, hu⟩ := h20 h20eq",
        "            rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp",
        "            subst hp; exact nvM6SatCnf_not_unsat hu",
        "          have hdom' : r = 0#64 ∨ r = 10#64 := by",
        "            rcases hdom with rfl | rfl | rfl",
        "            · exact Or.inl rfl",
        "            · exact Or.inr rfl",
        "            · exact False.elim (hne20 rfl)",
        "          refine ⟨hdom', hne20, fun hr10 => ?_⟩",
        "          obtain ⟨cnf, hp, hsat⟩ := h10 hr10",
        "          rw [parseDimacs_nvM6SatBytes, Option.some.injEq] at hp",
        "          subst hp; exact ⟨nvM6SatCnf_not_unsat, hsat⟩))",
        "  · rintro st (⟨hpc, rets, m', hQ, hrets, hmem⟩ | ⟨_, _, _, _, hX, _⟩)",
        "    · rcases rets with ⟨r, ⟨⟩⟩",
        f"      have hret : {arch.ret_gpr_expr} = r :=",
        f"        {arch.init_name}.retsIn_singleton r ({arch.targ}.mach.data st) hrets",
        "      rw [hret]",
        "      refine ⟨hpc, hQ.1, hQ.2.1, fun h10 => ?_⟩",
        "      obtain ⟨hnu, hf⟩ := hQ.2.2 h10",
        f"      exact ⟨hnu, hf _ ({arch.targ}.mach.mem ({arch.targ}.mach.data st)) hmem⟩",
        "    · exact False.elim hX",
        "",
        *alias_defs,
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


def build_plan(
    cfg: CertConfig, arches: list[str], cert_only: bool = False
) -> list[tuple[str, str]]:
    """Build deterministic `(relative_path, lean_source)` pairs and validate invariants."""
    files: list[tuple[str, str]] = []
    needs_bounds_file = (not cfg.no_bounds_import) or (
        bool(cfg.reuse_prefix) and cfg.reuse_mode == "pruned_relink"
    )
    for arch_key in arches:
        arch = ARCH_SPECS[arch_key]
        base = f"LeanQbe/T/{arch.dir_name}"
        if cert_only:
            planned = [(f"{base}/{cfg.prefix}Cert.lean", render_cert_ladder(cfg, arch))]
            files.extend(planned)
            continue
        planned: list[tuple[str, str]] = []
        if needs_bounds_file:
            planned.append((f"{base}/{cfg.prefix}Bounds.lean", render_bounds(cfg, arch)))
        for sl in cfg.slices:
            if sl.reuse_src_index is None:
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
        if cfg.hdr_model == "m6" and cfg.wrapper_mode == "full" and cfg.emit_sound:
            planned.append(
                (f"{base}/{cfg.prefix}Sound.lean", render_sound_wrapper(cfg, arch))
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

    if args.no_inlined:
        inl_mod = None
        inl_policy_mod = None
        inl_fns = None
        inl_mod_sym = None
        inl_policy = None
    else:
        inl_mod = args.inl_mod or (preset.inl_mod if preset else None)
        inl_policy_mod = args.inl_policy_mod or (
            preset.inl_policy_mod if preset else (f"{inl_mod}Policy" if inl_mod else None)
        )
        inl_fns = args.inl_fns or (
            preset.inl_fns if preset and preset.inl_fns else (f"{stem}InlFns" if inl_mod else None)
        )
        inl_mod_sym = args.inl_mod_sym or (
            preset.inl_mod_sym
            if preset and preset.inl_mod_sym
            else (f"{stem}InlMod" if inl_mod else None)
        )
        inl_policy = args.inl_policy or (
            preset.inl_policy
            if preset and preset.inl_policy
            else (f"{stem}InlPolicy" if inl_mod else None)
        )

    hdr_model = (
        args.hdr_model
        if args.hdr_model != "auto"
        else (preset.hdr_model if preset else "full")
    )
    sat_sound_mod = (
        args.sat_sound_mod
        if args.sat_sound_mod is not None
        else (preset.sat_sound_mod if preset else None)
    )
    sat_nv_mod = args.sat_nv_mod or (preset.sat_nv_mod if preset else None)
    source_ns = args.source_ns or (preset.source_ns if preset and preset.source_ns else source_mod)
    proof_ns = args.proof_ns or (preset.proof_ns if preset and preset.proof_ns else proof_mod)
    emit_sound = (
        args.emit_sound
        if args.emit_sound is not None
        else (preset.emit_sound if preset else True)
    )
    solve_spec_intro = args.solve_spec_intro or (
        preset.solve_spec_intro if preset else "fullM6SolveBytesCoreModelSpec_intro"
    )
    solve_spec_has_sat = (
        False
        if args.solve_spec_no_sat
        else (preset.solve_spec_has_sat if preset else True)
    )
    solve_bytes_suffix = args.solve_bytes_suffix or (
        preset.solve_bytes_suffix if preset else "_solve_bytes_iff.mpr"
    )
    solve_mem_thm = args.solve_mem_thm or (preset.solve_mem_thm if preset else None)
    max_dirs = (
        args.max_dirs
        if args.max_dirs is not None
        else (preset.default_max_dirs if preset else DEFAULT_MAX_DIRS)
    )

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
        if explicit_sizes is not None and not args.reuse_spec:
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

    flat: bool = (
        args.flat
        if args.flat is not None
        else (preset.default_flat if preset else False)
    )
    chunk_size: int = (
        args.chunk_size
        if args.chunk_size is not None
        else (
            preset.default_chunk_size
            if preset and preset.default_chunk_size is not None
            else (1 if flat else 4)
        )
    )
    workers: int = (
        args.workers
        if args.workers is not None
        else (
            preset.default_workers
            if preset and preset.default_workers is not None
            else (2 if flat else DEFAULT_WORKERS)
        )
    )
    max_slice_size: int | None = (
        args.max_slice_size
        if args.max_slice_size is not None
        else (preset.default_max_slice_size if preset else None)
    )

    uniform_slices = compute_slices(total_fns, args.slice_size, None)
    before_stats = compute_slice_stats(fn_metrics, uniform_slices, workers=workers)

    reuse_prefix: str | None = None
    reuse_inl_mod: str | None = None
    reuse_inl_fns: str | None = None
    reuse_bridge_mod: str | None = None
    reuse_thm_prefix: str | None = None
    reuse_mode: str = "verbatim"
    reuse_proof_mod: str | None = None
    reuse_proof_ns: str | None = None
    reuse_acyclic: str | None = None
    reuse_wf: str | None = None
    reuse_inl_mod_sym: str | None = None
    reuse_inl_policy: str | None = None
    cert_style: str = args.cert_style or (preset.default_cert_style if preset else "ladder")
    abi_common: bool = (
        args.abi_common
        if args.abi_common is not None
        else (preset.default_abi_common if preset else False)
    )
    cert_fns_sym = inl_fns if inl_mod and inl_fns else fns
    preset_cert_fns: str | None = None
    if preset is not None:
        preset_cert_fns = (
            preset.inl_fns
            if preset.inl_mod and preset.inl_fns
            else (preset.fns or f"{preset.stem}Fns")
        )
    fns_length_thm: str | None = args.fns_length_thm or (
        preset.fns_length_thm if preset is not None and cert_fns_sym == preset_cert_fns else None
    )
    if abi_common:
        if args.wrapper_mode == "full" and hdr_model != "m6":
            raise ValueError("--abi-common with --wrapper-mode full requires --hdr-model m6")
        if args.wrapper_mode == "full" and not inl_mod:
            raise ValueError("--abi-common with --wrapper-mode full requires an inlined module")
        if args.max_bound != 2048:
            raise ValueError("--abi-common requires --max-bound 2048")
    pin_cuts = load_pin_cuts(Path(args.pin_cuts), total_fns) if args.pin_cuts else None
    if args.reuse_spec:
        rspec = json.loads(Path(args.reuse_spec).read_text(encoding="utf-8"))
        reuse_prefix = args.reuse_prefix or rspec.get("reuse_prefix") or (
            preset.reuse_prefix if preset else None
        )
        if not reuse_prefix:
            raise ValueError("--reuse-spec requires reuse_prefix (in JSON, CLI, or preset)")
        reuse_prefix = str(reuse_prefix)
        reuse_inl_mod = args.reuse_inl_mod or rspec.get("reuse_inl_mod") or (
            preset.reuse_inl_mod if preset else None
        )
        reuse_inl_fns = args.reuse_inl_fns or rspec.get("reuse_inl_fns") or (
            preset.reuse_inl_fns if preset else None
        )
        if not reuse_inl_mod or not reuse_inl_fns:
            raise ValueError("--reuse-spec requires reuse_inl_mod and reuse_inl_fns")
        reuse_inl_mod = str(reuse_inl_mod)
        reuse_inl_fns = str(reuse_inl_fns)
        reuse_bridge_mod = args.reuse_bridge_mod or rspec.get("reuse_bridge_mod") or (
            preset.reuse_bridge_mod if preset else None
        )
        reuse_thm_prefix = args.reuse_thm_prefix or rspec.get("reuse_thm_prefix") or (
            preset.reuse_thm_prefix if preset else None
        )
        reuse_mode = args.reuse_mode or str(
            rspec.get("reuse_mode")
            or (preset.default_reuse_mode if preset else "pruned_relink")
        )
        if reuse_mode not in ("verbatim", "pruned_relink"):
            raise ValueError(f"unsupported reuse_mode '{reuse_mode}'")
        reuse_proof_mod = args.reuse_proof_mod or rspec.get("reuse_proof_mod") or (
            preset.reuse_proof_mod if preset else None
        )
        reuse_proof_ns = args.reuse_proof_ns or rspec.get("reuse_proof_ns") or (
            preset.reuse_proof_ns if preset else None
        )
        reuse_acyclic = args.reuse_acyclic or rspec.get("reuse_acyclic") or (
            preset.reuse_acyclic if preset else None
        )
        reuse_wf = args.reuse_wf or rspec.get("reuse_wf") or (
            preset.reuse_wf if preset else None
        )
        reuse_inl_mod_sym = args.reuse_inl_mod_sym or rspec.get("reuse_inl_mod_sym") or (
            preset.reuse_inl_mod_sym if preset else None
        )
        reuse_inl_policy = args.reuse_inl_policy or rspec.get("reuse_inl_policy") or (
            preset.reuse_inl_policy if preset else None
        )
        fresh_sizes = explicit_sizes
        if fresh_sizes is None and "fresh_sizes" in rspec:
            fresh_sizes = [int(x) for x in rspec["fresh_sizes"]]
        slices = plan_slices_with_reuse(
            fn_metrics,
            rspec["reused_slices"],
            slice_size=args.slice_size,
            workers=workers,
            balance=args.balance,
            singleton_size=args.singleton_size,
            singleton_work=args.singleton_work,
            max_slice_size=max_slice_size,
            heavy_thresh=args.heavy_thresh,
            fresh_sizes=fresh_sizes,
            max_slice_weight=args.max_slice_weight,
            singleton_weight=args.singleton_weight,
        )
    elif args.reuse_mode and args.reuse_mode != "verbatim":
        raise ValueError(f"--reuse-mode {args.reuse_mode} requires --reuse-spec")
    elif explicit_sizes is not None:
        slices = compute_slices(total_fns, args.slice_size, explicit_sizes)
    elif (
        max_slice_size is not None
        or args.singleton_size is not None
        or args.max_slice_weight is not None
    ):
        if (
            args.max_slice_weight is not None
            and args.max_slice_size is None
            and args.singleton_size is None
        ):
            sing_sz = 0
            sing_wk = args.singleton_work if args.singleton_work is not None else 0
            max_sz = 0
        else:
            sing_sz = args.singleton_size if args.singleton_size is not None else 350
            sing_wk = args.singleton_work if args.singleton_work is not None else sing_sz * 6
            max_sz = max_slice_size if max_slice_size is not None else 500
        raw_slices = singleton_isolated_slices(
            fn_metrics,
            singleton_size=sing_sz,
            singleton_work=sing_wk,
            max_slice_size=max_sz,
            max_slice_count=args.slice_size,
            max_slice_weight=args.max_slice_weight,
            singleton_weight=args.singleton_weight,
        )
        if pin_cuts:
            cut_ranges = apply_pin_cuts([(s.start, s.end) for s in raw_slices], pin_cuts)
            slices = tuple(
                SliceRange(index=idx, start=s, count=e - s)
                for idx, (s, e) in enumerate(cut_ranges, start=1)
            )
        else:
            slices = raw_slices
    elif args.balance:
        slices = autobalance_slices(
            fn_metrics,
            slice_size=args.slice_size,
            workers=workers,
            target_slices=args.target_slices,
            heavy_thresh=args.heavy_thresh,
            pin_cuts=pin_cuts,
        )
    else:
        if pin_cuts:
            cut_ranges = apply_pin_cuts([(s.start, s.end) for s in uniform_slices], pin_cuts)
            slices = tuple(
                SliceRange(index=idx, start=s, count=e - s)
                for idx, (s, e) in enumerate(cut_ranges, start=1)
            )
        else:
            slices = uniform_slices

    after_stats = compute_slice_stats(fn_metrics, slices, workers=workers)

    entry_idx = args.entry_idx if args.entry_idx is not None else total_fns - 1
    if not 0 <= entry_idx < total_fns:
        raise ValueError(f"--entry-idx {entry_idx} out of [0, {total_fns})")

    env = args.env or (preset.env if preset and preset.env else f"{stem}Env")
    module_ok = args.module_ok or (
        preset.module_ok if preset and preset.module_ok else f"{env}_moduleOk"
    )
    no_exit = args.no_exit or (
        preset.no_exit if preset and preset.no_exit else f"{env}_noExit"
    )
    unsat_env = args.unsat_env or env
    unsat_module_ok = args.unsat_module_ok or (
        module_ok if unsat_env == env else f"{unsat_env}_moduleOk"
    )
    unsat_no_exit = args.unsat_no_exit or (
        no_exit if unsat_env == env else f"{unsat_env}_noExit"
    )
    sound_env = args.sound_env or env
    sound_module_ok = args.sound_module_ok or (
        module_ok if sound_env == env else f"{sound_env}_moduleOk"
    )
    sound_no_exit = args.sound_no_exit or (
        no_exit if sound_env == env else f"{sound_env}_noExit"
    )

    prune_ext: bool = (
        args.prune_ext
        if args.prune_ext is not None
        else (preset.default_prune_ext if preset else False)
    )
    no_bounds_import: bool = (
        args.no_bounds_import
        if args.no_bounds_import is not None
        else (preset.default_no_bounds_import if preset else False)
    )
    if args.bounds_json:
        no_bounds_import = True
    bounds_literals = (
        load_bounds_json(Path(args.bounds_json), slices, total_fns) if args.bounds_json else None
    )
    tree_groups: int = (
        args.tree_groups
        if args.tree_groups is not None
        else (preset.default_tree_groups if preset else 0)
    )
    if tree_groups < 0:
        raise ValueError(f"--tree-groups must be >= 0, got {tree_groups}")
    if tree_groups >= 2 and cert_style != "slices":
        raise ValueError("--tree-groups >= 2 requires --cert-style slices")

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
        env=env,
        spec_table=args.spec_table or (preset.spec_table if preset and preset.spec_table else f"{stem}SpecTable"),
        spec_sigs=args.spec_sigs or (preset.spec_sigs if preset and preset.spec_sigs else f"{stem}SpecTable_sigs"),
        module_ok=module_ok,
        no_exit=no_exit,
        entry_const=args.entry_const or (preset.entry_const if preset else "Full.kissat_solve_bytes"),
        entry_fn=args.entry_fn or (preset.entry_fn if preset else "kissat_solve_bytes"),
        entry_spec=args.entry_spec or (preset.entry_spec if preset else "fullSolveBytesSpec"),
        entry_idx=entry_idx,
        total_fns=total_fns,
        slices=slices,
        chunk_size=chunk_size,
        max_dirs=max_dirs,
        max_bound=args.max_bound,
        wrapper_mode=args.wrapper_mode,
        print_axioms=args.print_axioms,
        fn_metrics=fn_metrics,
        before_stats=before_stats,
        after_stats=after_stats,
        inl_mod=inl_mod,
        inl_policy_mod=inl_policy_mod,
        inl_fns=inl_fns,
        inl_mod_sym=inl_mod_sym,
        inl_policy=inl_policy,
        sat_sound_mod=sat_sound_mod,
        sat_nv_mod=sat_nv_mod,
        hdr_model=hdr_model,
        emit_sound=emit_sound,
        unsat_env=unsat_env,
        unsat_module_ok=unsat_module_ok,
        unsat_no_exit=unsat_no_exit,
        sound_env=sound_env,
        sound_module_ok=sound_module_ok,
        sound_no_exit=sound_no_exit,
        source_ns=source_ns,
        proof_ns=proof_ns,
        solve_spec_intro=solve_spec_intro,
        solve_spec_has_sat=solve_spec_has_sat,
        solve_bytes_suffix=solve_bytes_suffix,
        solve_mem_thm=solve_mem_thm,
        reuse_prefix=reuse_prefix,
        reuse_inl_mod=reuse_inl_mod,
        reuse_inl_fns=reuse_inl_fns,
        reuse_bridge_mod=reuse_bridge_mod,
        reuse_thm_prefix=reuse_thm_prefix,
        reuse_mode=reuse_mode,
        reuse_proof_mod=reuse_proof_mod,
        reuse_proof_ns=reuse_proof_ns,
        reuse_acyclic=reuse_acyclic,
        reuse_wf=reuse_wf,
        reuse_inl_mod_sym=reuse_inl_mod_sym,
        reuse_inl_policy=reuse_inl_policy,
        cert_style=cert_style,
        abi_common=abi_common,
        fns_length_thm=fns_length_thm,
        prune_ext=prune_ext,
        no_bounds_import=no_bounds_import,
        bounds_literals=bounds_literals,
        tree_groups=tree_groups,
        max_slice_weight=args.max_slice_weight,
        flat=flat,
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
            "Solver preset name (e.g. FullFidelity, FullM8Opt, FullM7Fidelity, "
            "FullM7, FullM6, FullM5, FullM4, FullM3, FullFast, Full, Plain). "
            "Supplies canonical paths and defaults; explicit flags override them."
        ),
    )
    ap.add_argument(
        "--prefix",
        help="Certificate module prefix (e.g. KissatFidelity, KissatM8Opt, KissatPlain).",
    )
    ap.add_argument(
        "--arch",
        choices=("both", "amd64", "arm64"),
        default="both",
        help="Target architectures to generate (default: both).",
    )
    ap.add_argument("--root", default=".", help="Repository root for total-fn inference.")
    ap.add_argument("--out-dir", default=".", help="Output root directory (default: .).")
    ap.add_argument("--source-mod", help="Source Kissat module (e.g. ...FullM6).")
    ap.add_argument("--source-ns", help="Namespace exported by --source-mod (if different).")
    ap.add_argument("--proof-mod", help="Proof module (default: <source-mod>Proof).")
    ap.add_argument("--proof-ns", help="Namespace exported by --proof-mod (if different).")
    ap.add_argument("--inl-mod", help="Optional chunked/inlined module (e.g. ...FullM6Inl).")
    ap.add_argument("--inl-policy-mod", help="Inline policy module (e.g. ...FullM6InlPolicy).")
    ap.add_argument("--inl-fns", help="Inlined function list identifier (default: <stem>InlFns).")
    ap.add_argument("--inl-mod-sym", help="Inlined module identifier (default: <stem>InlMod).")
    ap.add_argument("--inl-policy", help="Inline policy identifier (default: <stem>InlPolicy).")
    ap.add_argument(
        "--no-inlined",
        action="store_true",
        help="Disable chunked inlined module mode even if preset defines --inl-mod.",
    )
    ap.add_argument("--sat-sound-mod", help="M6Hdr SAT+UNSAT soundness bridge module.")
    ap.add_argument("--sat-nv-mod", help="M6Hdr concrete non-vacuity witness module.")
    ap.add_argument(
        "--sound",
        dest="emit_sound",
        action="store_true",
        default=None,
        help="Emit `<Prefix>Sound.lean` wrapper for m6 model (default: per preset or on).",
    )
    ap.add_argument(
        "--no-sound",
        dest="emit_sound",
        action="store_false",
        help="Omit `<Prefix>Sound.lean` wrapper (UNSAT-only).",
    )
    ap.add_argument(
        "--solve-spec-intro",
        help="Intro constructor lemma for solve bytes spec (default: fullM6SolveBytesCoreModelSpec_intro).",
    )
    ap.add_argument(
        "--solve-spec-no-sat",
        action="store_true",
        help="Solve spec intro callback takes 6 args (no SAT model hypothesis).",
    )
    ap.add_argument(
        "--solve-mem-thm",
        help="Optional `<entry_const> ∈ <mod>.fns` theorem (avoids `t_kernel_rfl`).",
    )
    ap.add_argument(
        "--hdr-model",
        choices=("auto", "full", "m6"),
        default="auto",
        help="Workspace header & soundness wrapper model (auto|full|m6, default: auto).",
    )
    ap.add_argument("--stem", help="Identifier stem (e.g. m4, m5, m6, m7).")
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
    ap.add_argument("--unsat-env", help="Override UNSAT non-vacuity environment.")
    ap.add_argument("--unsat-module-ok", help="Override UNSAT non-vacuity ModuleOk.")
    ap.add_argument("--unsat-no-exit", help="Override UNSAT non-vacuity noExit.")
    ap.add_argument("--sound-env", help="Override SAT+UNSAT soundness environment.")
    ap.add_argument("--sound-module-ok", help="Override SAT+UNSAT soundness ModuleOk.")
    ap.add_argument("--sound-no-exit", help="Override SAT+UNSAT soundness noExit.")
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
        "--max-slice-count",
        dest="slice_size",
        type=int,
        default=MAX_SLICE_SIZE,
        help=f"Max functions per slice, 1..{MAX_SLICE_SIZE} (default: {MAX_SLICE_SIZE}).",
    )
    ap.add_argument(
        "--max-slice-size",
        type=int,
        default=None,
        help="Optional max cumulative IR size per multi-fn slice (enables singleton isolation).",
    )
    ap.add_argument(
        "--max-slice-weight",
        type=float,
        default=None,
        help="Optional max cumulative weighted cost per multi-fn micro-slice (N6).",
    )
    ap.add_argument(
        "--singleton-weight",
        type=float,
        default=None,
        help=(
            "Optional function cost floor isolating heavy singletons "
            "(default: 0.65 * max_slice_weight)."
        ),
    )
    ap.add_argument(
        "--prune-ext",
        dest="prune_ext",
        action="store_true",
        default=None,
        help=(
            "Emit `(pruneExt := true)` on `compile_linked_chunks!` "
            "(N4; default: on for FullFidelity)."
        ),
    )
    ap.add_argument(
        "--no-prune-ext",
        dest="prune_ext",
        action="store_false",
        help="Disable `(pruneExt := true)` on `compile_linked_chunks!`.",
    )
    ap.add_argument(
        "--no-bounds-import",
        dest="no_bounds_import",
        action="store_true",
        default=None,
        help=(
            "Drop monolithic `<Prefix>Bounds.lean` import from `Cert2..N` and emit "
            "per-slice pruned bounds (N2; default: on for FullFidelity)."
        ),
    )
    ap.add_argument(
        "--bounds-import",
        dest="no_bounds_import",
        action="store_false",
        help="Force monolithic `<Prefix>Bounds.lean` import across `Cert2..N`.",
    )
    ap.add_argument(
        "--bounds-json",
        help=(
            "Optional JSON file providing per-slice/per-fn bounds for pure literal "
            "`slice{k}Ext` (N2)."
        ),
    )
    ap.add_argument(
        "--tree-groups",
        type=int,
        default=None,
        help=(
            "Partition slices into N super-groups for a 2-level balanced `checkLinkList` "
            "tree via `LinkedCert.ofCheckedGroups` (N6; requires `--cert-style slices`)."
        ),
    )
    ap.add_argument(
        "--singleton-size",
        type=int,
        default=None,
        help="Optional IR size floor isolating heavy functions as singletons (e.g. 350).",
    )
    ap.add_argument(
        "--singleton-work",
        type=int,
        default=None,
        help="Optional Rega lookahead work floor isolating heavy singletons (default: 6*singleton_size).",
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
        "--reuse-spec",
        help="Optional JSON spec naming reused slices from a sibling cert family.",
    )
    ap.add_argument("--reuse-prefix", help="Override reused cert prefix (e.g. KissatFidelity).")
    ap.add_argument("--reuse-inl-mod", help="Override reused inlined module.")
    ap.add_argument("--reuse-inl-fns", help="Override reused inlined fn list identifier.")
    ap.add_argument("--reuse-inl-mod-sym", help="Override reused inlined module identifier.")
    ap.add_argument("--reuse-inl-policy", help="Override reused inlined policy identifier.")
    ap.add_argument("--reuse-proof-mod", help="Override reused proof module.")
    ap.add_argument("--reuse-proof-ns", help="Override reused proof namespace.")
    ap.add_argument("--reuse-acyclic", help="Override reused acyclic theorem.")
    ap.add_argument("--reuse-wf", help="Override reused wf theorem.")
    ap.add_argument("--reuse-bridge-mod", help="Override reused slice-equality bridge module.")
    ap.add_argument("--reuse-thm-prefix", help="Override reused bridge theorem prefix.")
    ap.add_argument(
        "--reuse-mode",
        choices=("verbatim", "pruned_relink"),
        default=None,
        help=(
            "Reuse linking strategy with --reuse-spec: 'verbatim' (direct chunk reuse) "
            "or 'pruned_relink' (MainLinkReuseCover + eval_raw_callees!/eval_pruned_ext!)."
        ),
    )
    ap.add_argument(
        "--pin-cuts",
        help="Optional JSON file of fn-index cut boundaries to split slices cleanly.",
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
        default=None,
        help=(
            f"Parallel worker count for LPT bin packing "
            f"(default: 2 for --flat/FullFidelityStep11, else {DEFAULT_WORKERS})."
        ),
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
    ap.add_argument(
        "--chunk-size",
        type=int,
        default=None,
        help="Chunk size (default: 1 for --flat/FullFidelityStep11, else 4).",
    )
    ap.add_argument(
        "--flat",
        dest="flat",
        action="store_true",
        default=None,
        help=(
            "Emit first-order `MainCertFlat`/`MainCertFlatElab` imports and "
            "`(flat := true)` on cert slices and bounds (default: on for FullFidelityStep11)."
        ),
    )
    ap.add_argument(
        "--no-flat",
        dest="flat",
        action="store_false",
        help="Disable `(flat := true)` flat kernel path even if preset enables it.",
    )
    ap.add_argument(
        "--max-dirs",
        type=int,
        default=None,
        help="maxDirs (default: 600 for FullM6/FullM7, else 450).",
    )
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
        "--cert-style",
        choices=("ladder", "slices"),
        default=None,
        help=(
            "Certificate assembly style in <Prefix>Cert.lean: 'ladder' or "
            "O(1)-boilerplate 'slices' (LinkedCert.ofChunkSlices). Default: per "
            "preset (FullFidelity/FullM8Opt: slices), else ladder."
        ),
    )
    ap.add_argument(
        "--abi-common",
        dest="abi_common",
        action="store_true",
        default=None,
        help=(
            "Delegate <Prefix>CertLink.lean and M6Hdr <Prefix>.lean proofs to "
            "arch-free KissatCertCommon + {Amd64,Arm64}.KissatAbi. Default: per "
            "preset (FullFidelity/FullM8Opt: on), else off."
        ),
    )
    ap.add_argument(
        "--no-abi-common",
        dest="abi_common",
        action="store_false",
        help="Emit inline per-arch CertLink/Top proofs (overrides a preset default).",
    )
    ap.add_argument(
        "--fns-length-thm",
        help="`<cert_fns>.length = total` theorem for --cert-style slices (default: per preset).",
    )
    ap.add_argument(
        "--solve-bytes-suffix",
        help="Override `<env><suffix>` bridge for M6Hdr solve spec (default: preset or _solve_bytes_iff.mpr).",
    )
    ap.add_argument(
        "--cert-only",
        action="store_true",
        help="Emit only `<Prefix>Cert.lean` without regenerating Bounds/Cert1..N/CertLink/Top.",
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
        files = build_plan(cfg, arches, cert_only=args.cert_only)
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
