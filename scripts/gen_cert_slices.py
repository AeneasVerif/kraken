#!/usr/bin/env python3
"""Deterministic CLI generator for flat 1-tier Kissat solver cert slices.

Generates five Lean module families per architecture (`Amd64`, `Arm64`):
  1. `<Prefix>Bounds.lean`     - `eval_prefix_ext!` + `<stem>ExtPrefix`
  2. `<Prefix>Cert1..N.lean`   - `<= 12` fns/slice (`compile_linked_chunks!`)
  3. `<Prefix>Cert.lean`       - flat `LinkedCert.append` ladder
  4. `<Prefix>CertLink.lean`   - `<stem>_legalSig`, `mk_module_fnspec`,
                                 `solve_{x64,arm64}_of_fnspec`
  5. `<Prefix>.lean`           - compiled cert alias, `*_module_fnspec`,
                                 and UNSAT correctness wrappers

All generated files strictly honor the 100-column repository line limit and
deterministic layout (zero timestamps or nondeterministic ordering).
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass
from pathlib import Path

MAX_LINE_LEN = 100
MAX_SLICE_SIZE = 12


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
    ),
}


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
class CertConfig:
    """Resolved deterministic generation configuration."""

    prefix: str
    stem: str
    camel_prefix: str
    source_mod: str
    proof_mod: str
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
            f"`{cfg.total_fns}` functions of `{cfg.source_mod}.{cfg.fns}` via "
            "`eval_prefix_ext!`, enabling flat 1-tier parallel slice certificates "
            "via `<prefix>ExtPrefix`."
        ),
        "-/",
        "",
        "set_option autoImplicit false",
        "",
        "@[expose] public section",
        "",
        f"namespace {ns}",
        "",
        f"open LeanQbe.T {arch.ns_prefix} {cfg.source_mod}",
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
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_cert_link(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>CertLink.lean` with `legalSig`, `mk_module_fnspec`, `solve_*`."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}CertLink"
    cert_mod = f"{arch.ns_prefix}.{cfg.prefix}Cert"

    if arch.key == "amd64":
        solve_block = [
            f"/-- Lifting any `FnSpec` for `\"{cfg.entry_fn}\"` at stack bound "
            "`b` and contract",
            f"`spec` to Kraken-x64 `Eventually` via `x64_of_returns`. -/",
            "theorem solve_x64_of_fnspec {b : Nat}",
            "    {spec : Spec [i64, i64, i64, i64, i64] [i64]}",
            f"    (hfnspec : x64Target.FnSpec hh \"{cfg.entry_fn}\" spec b 0)",
            "    (cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64)",
            "    {m : Mem 64} {Q : Post [i64]}",
            "    (hspec : spec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q",
            "      (fun _ _ _ _ => False))",
            "    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)",
            "    (hrdi : s.regs.get64 .rdi = cnf_ptr)",
            "    (hrsi : s.regs.get64 .rsi = cnf_len)",
            "    (hrdx : s.regs.get64 .rdx = work_ptr)",
            "    (hrcx : s.regs.get64 .rcx = work_len)",
            "    (hr8 : s.regs.get64 .r8 = fuel)",
            "    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)",
            "    (hmem : s.dmem =⋆ Eq m ⋆",
            "      (region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆",
            "        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :",
            "    Eventually (step1 Host.exe)",
            "      (fun st =>",
            "        st.pc = ra ∧",
            "        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],",
            "          st.data.regs.get64 r = s.regs.get64 r) ∧",
            "        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧",
            "        ∃ m', Q (st.data.regs.get64 .rax, ()) m' ∧",
            "          (st.data.dmem =⋆ Eq m' ⋆",
            "            region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8) ⋆ R))",
            f"      ⟨s, Labels.label \"{cfg.entry_fn}\"⟩ := by",
            "  have hargs : x64Target.ArgsIn (as := [i64, i64, i64, i64, i64])",
            "      (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) s :=",
            "    ⟨_, rfl,",
            "      .cons ⟨by decide, by simpa using hrdi⟩",
            "        (.cons ⟨by decide, by simpa using hrsi⟩",
            "          (.cons ⟨by decide, by simpa using hrdx⟩",
            "            (.cons ⟨by decide, by simpa using hrcx⟩",
            "              (.cons ⟨by decide, by simpa using hr8⟩ .nil))))⟩",
            "  refine eventually_weaken _ _ _ _ ?_",
            "    (x64_of_returns hfnspec hspec s ra R hargs hsp hmem)",
            "  rintro st ⟨hpc, hcs, hsp', rets, m', hQ, hrets, hm'⟩",
            "  rcases rets with ⟨r, ⟨⟩⟩",
            "  have hrax : st.data.regs.get64 .rax = r :=",
            "    x64Init.retsIn_singleton r st.data hrets",
            "  rw [hrax]",
            "  exact ⟨hpc, hcs, hsp', m', hQ, hm'⟩",
        ]
    else:
        solve_block = [
            f"/-- Lifting any `FnSpec` for `\"{cfg.entry_fn}\"` at stack bound "
            "`b` and contract",
            f"`spec` to Kraken-AArch64 `Eventually` via `arm64_of_returns`. -/",
            "theorem solve_arm64_of_fnspec {b : Nat}",
            "    {spec : Spec [i64, i64, i64, i64, i64] [i64]}",
            f"    (hfnspec : armTarget.FnSpec hh \"{cfg.entry_fn}\" spec b 0)",
            "    (cnf_ptr cnf_len work_ptr work_len fuel : BitVec 64)",
            "    {m : Mem 64} {Q : Post [i64]}",
            "    (hspec : spec (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) m Q",
            "      (fun _ _ _ _ => False))",
            "    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)",
            "    (hx0 : (s.regs.getXReg .X0).toBitVec = cnf_ptr)",
            "    (hx1 : (s.regs.getXReg .X1).toBitVec = cnf_len)",
            "    (hx2 : (s.regs.getXReg .X2).toBitVec = work_ptr)",
            "    (hx3 : (s.regs.getXReg .X3).toBitVec = work_len)",
            "    (hx4 : (s.regs.getXReg .X4).toBitVec = fuel)",
            "    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)",
            "    (hmem : s.dmem =⋆ Eq m ⋆",
            "      region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R) :",
            "    Eventually (step1 Host.exe)",
            "      (fun st =>",
            "        st.pc = ra ∧",
            "        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,",
            "            .X27, .X28, .X29],",
            "          st.data.regs.getXReg r = s.regs.getXReg r) ∧",
            "        st.data.regs.SP = s.regs.SP ∧",
            "        ∃ m', Q ((st.data.regs.getXReg .X0).toBitVec, ()) m' ∧",
            "          (st.data.dmem =⋆ Eq m' ⋆",
            "            region (s.regs.SP.toBitVec - BitVec.ofNat 64 b) b ⋆ R))",
            f"      ⟨s, Labels.label \"{cfg.entry_fn}\"⟩ := by",
            "  have hargs : armTarget.ArgsIn (as := [i64, i64, i64, i64, i64])",
            "      (cnf_ptr, cnf_len, work_ptr, work_len, fuel, ()) s :=",
            "    ⟨_, rfl,",
            "      .cons ⟨by decide, by simpa [get_reg] using hx0⟩",
            "        (.cons ⟨by decide, by simpa [get_reg] using hx1⟩",
            "          (.cons ⟨by decide, by simpa [get_reg] using hx2⟩",
            "            (.cons ⟨by decide, by simpa [get_reg] using hx3⟩",
            "              (.cons ⟨by decide, by simpa [get_reg] using hx4⟩ .nil))))⟩",
            "  refine eventually_weaken _ _ _ _ ?_",
            "    (arm64_of_returns hfnspec hspec s ra R hargs hra hsp hmem)",
            "  rintro st ⟨hpc, hcal, hsp', rets, m', hQ, hrets, hm'⟩",
            "  rcases rets with ⟨r, ⟨⟩⟩",
            "  have hx0' : (st.data.regs.getXReg .X0).toBitVec = r := by",
            "    simpa [armInit, get_reg] using armInit.retsIn_singleton r st.data hrets",
            "  rw [hx0']",
            "  exact ⟨hpc, hcal, hsp', m', hQ, hm'⟩",
        ]

    lines = [
        "module",
        "",
        f"public import {cert_mod}",
        "import all Kraken.Mem",
        "import all Kraken.Separation",
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
        "",
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_top_wrapper(cfg: CertConfig, arch: ArchSpec) -> str:
    """Render `<Prefix>.lean` combining cert, link helpers, and proof."""
    ns = f"{arch.ns_prefix}.{cfg.prefix}"
    cert_mod = f"{arch.ns_prefix}.{cfg.prefix}Cert"
    link_mod = f"{arch.ns_prefix}.{cfg.prefix}CertLink"
    compiled_name = f"{cfg.camel_prefix}_compiled_{arch.arch_tag}"
    compiled_ty = (
        f"LinkedCert {arch.targ} {arch.layout} {arch.lt} {arch.cl} {cfg.mod}"
    )

    pub_imports = [
        f"public import {cert_mod}",
        f"public import {link_mod}",
    ]
    if cfg.wrapper_mode != "compiled":
        pub_imports.append(f"public import {cfg.proof_mod}")

    priv_imports = [f"import {arch.lemmas_mod}"]
    if cfg.wrapper_mode == "full":
        priv_imports.append("import all Std.Sat.CNF.Basic")
    priv_imports.extend(["import all Kraken.Mem", "import all Kraken.Separation"])

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
        f"@[reducible] noncomputable def {compiled_name} :",
        f"    {compiled_ty} :=",
        f"  {cfg.prefix}Cert.{cfg.cert_name}",
        "",
    ]

    if cfg.wrapper_mode in ("fnspec", "full"):
        body.extend(
            [
                *wrap_comment_lines(
                    f"/-- Unconditional whole-module `Defined` + `FnSpec` for "
                    f"all `{cfg.total_fns}` functions in `{cfg.mod}` under "
                    f"`{cfg.env}` on {arch.isa_title}. -/"
                ),
                f"theorem {cfg.stem}_module_fnspec [hh : Host] (k₀ : Nat)",
                f"    (hc : {compiled_name}.code.IsInfixAt Host.prog k₀)",
                "    (hu : Host.LabelsUnique)",
                f"    {{f : Fn}} (hf : f ∈ {cfg.mod}.fns) :",
                f"    {arch.targ}.Defined hh f.name ∧",
                f"      {arch.targ}.FnSpec hh f.name ({cfg.env} f.name f.as f.rs)",
                f"        ({compiled_name}.bound f.name) 0 := by",
                f"  refine {cfg.prefix}CertLink.mk_module_fnspec {cfg.env}",
                "    (fun g hg args m Q X hs => ?)",
                f"    (fun g _ => {cfg.no_exit} g.name g.as g.rs) k₀ hc hu hf",
                "  obtain ⟨pre, post, hsp⟩ := List.mem_iff_append.mp hg",
                f"  exact ({cfg.module_ok}.fnsOk pre g post hsp).2.2 args m Q X hs",
                "",
            ]
        )

    if cfg.wrapper_mode == "full":
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
                *render_unsat_section(cfg, arch, compiled_name),
            ]
        )

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
        f"end {ns}",
        "",
    ]
    return "\n".join(lines)


def render_unsat_section(
    cfg: CertConfig, arch: ArchSpec, compiled_name: str
) -> list[str]:
    """Render UNSAT soundness and answer-only wrappers for `Amd64` / `Arm64`."""
    unsat_thm = f"{cfg.stem}_solve_bytes_unsat_{arch.arch_tag}"
    sound_thm = f"{cfg.stem}_solve_bytes_unsat_sound_{arch.arch_tag}"
    entry_label = f"Labels.label \"{cfg.entry_fn}\""
    bound_expr = f"({compiled_name}.bound \"{cfg.entry_fn}\")"

    if arch.key == "amd64":
        return [
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
            "include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit "
            "s ra R",
            "  hrdi hrsi hrdx hrcx hr8 hsp hmem",
            "",
            *wrap_comment_lines(
                f"/-- Unconditional end-to-end {arch.isa_title} UNSAT soundness "
                f"for `{cfg.mod}`. -/"
            ),
            f"theorem {unsat_thm} :",
            "    Eventually (step1 Host.exe)",
            "      (fun st =>",
            "        st.pc = ra ∧",
            "        (st.data.regs.get64 .rax = 0#64 ∨",
            "          st.data.regs.get64 .rax = 10#64 ∨",
            "          st.data.regs.get64 .rax = 20#64) ∧",
            "        (st.data.regs.get64 .rax = 20#64 →",
            "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
            "        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],",
            "          st.data.regs.get64 r = s.regs.get64 r) ∧",
            "        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧",
            "        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
            "          region (s.regs.get64 .rsp - BitVec.ofNat 64",
            f"              {bound_expr})",
            f"            ({bound_expr} + 8) ⋆ R)",
            "          st.data.dmem)",
            f"      ⟨s, {entry_label}⟩ := by",
            f"  have hfn := ({cfg.stem}_module_fnspec k₀ hc hu "
            f"solve_in_{cfg.mod}).2",
            "  rcases hmem with ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, hm_in, hc0⟩, "
            "hm_r⟩",
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
            f"    Env.ofTable_of_mem",
            f"      (List.mem_of_getElem? (rfl : "
            f"({cfg.spec_table} _)[{cfg.entry_idx}]? = some _))",
            f"      ({cfg.spec_table}_nodup {cfg.entry_spec})",
            "      ⟨cnfBytes, wlen, emp, rfl, rfl, hcfit, hwfit,",
            "        by rw [sep_emp]; exact hm_in,",
            "        fun _ _ h u' m' =>",
            "          by rw [sep_emp] at m'; exact ⟨h, u', m'⟩⟩",
            "  refine eventually_weaken _ _ _ _ ?_",
            f"    ({cfg.prefix}CertLink.solve_x64_of_fnspec hfn cnf_ptr _ "
            "work_ptr _ fuel",
            "      hspec s ra R hrdi hrsi hrdx hrcx hr8 hsp",
            "      ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, rfl, hc0⟩, hm_r⟩)",
            "  rintro st ⟨hpc, hcal, hrsp, m', ⟨hdom, hu', hm'⟩,",
            "    ⟨ma, mr2, u3, d3, ⟨_, ms2, u4, d4, rfl, hs⟩, hr⟩⟩",
            "  exact ⟨hpc, hdom, hu', hcal, hrsp,",
            "    ⟨ma, mr2, u3, d3, ⟨m', ms2, u4, d4, hm', hs⟩, hr⟩⟩",
            "",
            *wrap_comment_lines(
                f"/-- Answer-only {arch.isa_title} UNSAT soundness corollary "
                f"for `{cfg.mod}`. -/"
            ),
            f"theorem {sound_thm} :",
            "    Eventually (step1 Host.exe)",
            "      (fun st =>",
            "        st.pc = ra ∧",
            "        (st.data.regs.get64 .rax = 0#64 ∨",
            "          st.data.regs.get64 .rax = 10#64 ∨",
            "          st.data.regs.get64 .rax = 20#64) ∧",
            "        (st.data.regs.get64 .rax = 20#64 →",
            "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))",
            f"      ⟨s, {entry_label}⟩ :=",
            "  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)",
            f"    ({unsat_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen "
            "hcfit hwfit",
            "      s ra R hrdi hrsi hrdx hrcx hr8 hsp hmem)",
            "",
            "end Unsat",
            "",
        ]
    return [
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
        "include hh k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen hcfit hwfit "
        "s ra R",
        "  hx0 hx1 hx2 hx3 hx4 hra hsp hmem",
        "",
        *wrap_comment_lines(
            f"/-- Unconditional end-to-end {arch.isa_title} UNSAT soundness "
            f"for `{cfg.mod}`. -/"
        ),
        f"theorem {unsat_thm} :",
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        "        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨",
        "          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨",
        "          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧",
        "        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) ∧",
        "        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26,",
        "            .X27, .X28, .X29],",
        "          st.data.regs.getXReg r = s.regs.getXReg r) ∧",
        "        st.data.regs.SP = s.regs.SP ∧",
        "        (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆",
        "          region (s.regs.SP.toBitVec - BitVec.ofNat 64",
        f"              {bound_expr})",
        f"            {bound_expr} ⋆ R)",
        "          st.data.dmem)",
        f"      ⟨s, {entry_label}⟩ := by",
        f"  have hfn := ({cfg.stem}_module_fnspec k₀ hc hu "
        f"solve_in_{cfg.mod}).2",
        "  rcases hmem with ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, hm_in, hc0⟩, "
        "hm_r⟩",
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
        f"    ({cfg.prefix}CertLink.solve_arm64_of_fnspec hfn cnf_ptr _ "
        "work_ptr _ fuel",
        "      hspec s ra R hx0 hx1 hx2 hx3 hx4 hra hsp",
        "      ⟨ms, mr, u1, d1, ⟨m, mc, u2, d2, rfl, hc0⟩, hm_r⟩)",
        "  rintro st ⟨hpc, hcal, hsp', m', ⟨hdom, hu', hm'⟩,",
        "    ⟨ma, mr2, u3, d3, ⟨_, ms2, u4, d4, rfl, hs⟩, hr⟩⟩",
        "  exact ⟨hpc, hdom, hu', hcal, hsp',",
        "    ⟨ma, mr2, u3, d3, ⟨m', ms2, u4, d4, hm', hs⟩, hr⟩⟩",
        "",
        *wrap_comment_lines(
            f"/-- Answer-only {arch.isa_title} UNSAT soundness corollary for "
            f"`{cfg.mod}`. -/"
        ),
        f"theorem {sound_thm} :",
        "    Eventually (step1 Host.exe)",
        "      (fun st =>",
        "        st.pc = ra ∧",
        "        ((st.data.regs.getXReg .X0).toBitVec = 0#64 ∨",
        "          (st.data.regs.getXReg .X0).toBitVec = 10#64 ∨",
        "          (st.data.regs.getXReg .X0).toBitVec = 20#64) ∧",
        "        ((st.data.regs.getXReg .X0).toBitVec = 20#64 →",
        "          ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat))",
        f"      ⟨s, {entry_label}⟩ :=",
        "  eventually_weaken _ _ _ _ (fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩)",
        f"    ({unsat_thm} k₀ hc hu cnf_ptr work_ptr fuel cnfBytes wlen "
        "hcfit hwfit",
        "      s ra R hx0 hx1 hx2 hx3 hx4 hra hsp hmem)",
        "",
        "end Unsat",
        "",
    ]


def build_plan(cfg: CertConfig, arches: list[str]) -> list[tuple[str, str]]:
    """Build deterministic `(relative_path, lean_source)` pairs."""
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
        for rel_path, content in planned:
            check_line_lengths(rel_path, content)
            files.append((rel_path, content))
    return files


def build_config(args: argparse.Namespace) -> CertConfig:
    """Resolve CLI options and defaults into a validated `CertConfig`."""
    prefix: str = args.prefix
    if not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", prefix):
        raise ValueError(f"invalid --prefix identifier: {prefix}")

    stem = args.stem or infer_stem(prefix)
    source_mod = args.source_mod or infer_source_mod(prefix, stem)
    proof_mod = args.proof_mod or f"{source_mod}Proof"
    fns = args.fns or f"{stem}Fns"
    mod = args.mod or f"{stem}Module"
    root = Path(args.root).resolve()

    explicit_sizes: list[int] | None = None
    if args.slice_sizes:
        explicit_sizes = [int(x.strip()) for x in args.slice_sizes.split(",") if x.strip()]

    total_fns = args.total_fns
    if total_fns is None:
        if explicit_sizes is not None:
            total_fns = sum(explicit_sizes)
        else:
            total_fns = detect_total_fns(root, source_mod, fns)
    if total_fns is None:
        raise ValueError(
            f"cannot infer --total-fns from {source_mod}; pass --total-fns N explicitly"
        )

    slices = compute_slices(total_fns, args.slice_size, explicit_sizes)
    entry_idx = args.entry_idx if args.entry_idx is not None else total_fns - 1
    if not 0 <= entry_idx < total_fns:
        raise ValueError(f"--entry-idx {entry_idx} out of [0, {total_fns})")

    return CertConfig(
        prefix=prefix,
        stem=stem,
        camel_prefix=lower_camel(prefix),
        source_mod=source_mod,
        proof_mod=proof_mod,
        fns=fns,
        mod=mod,
        cert_name=args.cert_name or f"{stem}Cert",
        acyclic=args.acyclic or f"{stem}_acyclic",
        wf=args.wf or f"{fns}_wf",
        env=args.env or f"{stem}Env",
        spec_table=args.spec_table or f"{stem}SpecTable",
        spec_sigs=args.spec_sigs or f"{stem}SpecTable_sigs",
        module_ok=args.module_ok or f"{stem}Env_moduleOk",
        no_exit=args.no_exit or f"{stem}Env_noExit",
        entry_const=args.entry_const,
        entry_fn=args.entry_fn,
        entry_spec=args.entry_spec,
        entry_idx=entry_idx,
        total_fns=total_fns,
        slices=slices,
        chunk_size=args.chunk_size,
        max_dirs=args.max_dirs,
        max_bound=args.max_bound,
        wrapper_mode=args.wrapper_mode,
    )


def parse_args(argv: list[str] | None = None) -> argparse.Namespace:
    """Parse CLI arguments."""
    ap = argparse.ArgumentParser(
        description="Deterministic generator for flat 1-tier LeanQbe solver cert slices."
    )
    ap.add_argument(
        "--prefix",
        required=True,
        help="Certificate module prefix (e.g. KissatM3, KissatM4, KissatM5).",
    )
    ap.add_argument(
        "--arch",
        choices=("both", "amd64", "arm64"),
        default="both",
        help="Target architecture(s) to generate (default: both).",
    )
    ap.add_argument("--root", default=".", help="Repo root for auto-detecting fns count.")
    ap.add_argument(
        "--out-dir",
        default=".",
        help="Output root directory (default: . -> LeanQbe/T/<Arch>/...).",
    )
    ap.add_argument("--source-mod", help="Solver IL module (e.g. ...FullM4).")
    ap.add_argument("--proof-mod", help="Solver proof module (default: <source-mod>Proof).")
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
        default="Full.kissat_solve_bytes",
        help="Entry Fn constant for solve wrappers.",
    )
    ap.add_argument(
        "--entry-fn",
        default="kissat_solve_bytes",
        help="Entry C/QBE symbol name (default: kissat_solve_bytes).",
    )
    ap.add_argument(
        "--entry-spec",
        default="fullSolveBytesSpec",
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
        help="Comma-separated explicit slice sizes (each <= 12).",
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
    slice_desc = ", ".join(
        f"S{s.index}=[{s.start},{s.end})({s.count})" for s in cfg.slices
    )
    mode = "dry-run" if args.dry_run else "write"
    print(
        f"gen_cert_slices ({mode}): prefix={cfg.prefix} total_fns={cfg.total_fns} "
        f"slices={len(cfg.slices)} arch={args.arch} files={len(files)} "
        f"max_line={max_len}c"
    )
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
