/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.ExportCnfEntry
public import LeanQbe.T.Examples.Kissat.ExportCnfStateProof
public import LeanQbe.T.Examples.Kissat.Proof.Spec.SatNv
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Logic.BitVec
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Logic.Rules
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import Kraken.Mem
import Kraken.Separation

/-!
# Verified Simplified-CNF Exporter — Shard E3 Helpers & Sub-Function WP (`ExportCnfEntryProof0`)

Shared DIMACS helpers, `KissatExportOut` layout predicate, `FullM6Hdr` workspace &
`XPost`-polymorphic `Spec` contracts, and WP proofs for `kissat_emit_trivial_cnf_bytes` and
`kissat_simplify_export_loaded` (zero dependency on `FullM6Proof`, `FullM6SatSound`, or
`FullM6OrchProof2`). Top-level entry theorems live in `ExportCnfEntryProof`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.ExportCnfEntryProof

open Std.Sat
open Kraken
open Kraken.Bedrock2.Test
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Src
open LeanQbe.T.Examples.Kissat.Ref hiding isDimacsWs isDimacsDigit dimacsBound
  skipWsCommentsAux skipWsComments skipWs skipWs1 parseDigitsAux parseNat
  parseHeader parseClauseAux parseClause parseClauses parseDimacs
open LeanQbe.T.Examples.Kissat.Proof.Spec hiding
  fullM6WorkBase fullM6WorkHdr m6ExtAddr_fullM6WorkHdr
  region_work_to_m6_workBase region_work_from_m6_hdrMem
  fullM6PreprocessSpec fullM6PreprocessSpec_of fullM6PreprocessSpec_monoX
open LeanQbe.T.Examples.Kissat.ExportCnfFmt
open LeanQbe.T.Examples.Kissat.ExportCnfState
open LeanQbe.T.Examples.Kissat.ExportCnfEntry

/-! ## 1. Pure DIMACS Constants, `KissatExportOut` Layout, & State Helpers -/

@[expose] public section

/-- Canonical ASCII contradiction DIMACS bytes `"p cnf 0 1\n0\n"` (`12` bytes). -/
def unsatDimacsBytes : List UInt8 :=
  emitDimacsHdrBytes 0 1 ++ [asciiZero, asciiNewline]

/-- Canonical ASCII empty-SAT DIMACS bytes `"p cnf 0 0\n"` (`10` bytes). -/
def satEmptyDimacsBytes : List UInt8 :=
  emitDimacsHdrBytes 0 0

/-- 24-byte `KissatExportOut` struct `{ u64 out_ptr; u64 out_cap; u64 out_len; }`. -/
def exportOutMem (outDesc outPtr outCap outLen : BitVec 64) : Mem 64 → Prop :=
  cell64 outDesc outPtr ⋆
  cell64 (outDesc + 8#64) outCap ⋆
  cell64 (outDesc + 16#64) outLen

/-- Aligned base address of the `M6Hdr` workspace (`work_ptr + fullAlignPad work_ptr`). -/
def fullM6WorkBase (work_ptr : BitVec 64) : BitVec 64 :=
  work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr)

/-- Aligned `FullHdr *h` pointer placed `fullM6ExtBytes = 2304` bytes past `fullM6WorkBase`. -/
def fullM6WorkHdr (work_ptr : BitVec 64) : BitVec 64 :=
  fullM6WorkBase work_ptr + BitVec.ofNat 64 fullM6ExtBytes

end

public section

theorem m6ExtAddr_fullM6WorkHdr (work_ptr : BitVec 64) :
    m6ExtAddr (fullM6WorkHdr work_ptr) = fullM6WorkBase work_ptr := by
  rw [m6ExtAddr_eq]
  unfold fullM6WorkHdr fullM6ExtBytes
  exact BitVec.add_sub_cancel (fullM6WorkBase work_ptr) (BitVec.ofNat 64 2304)

/-- Split `region work_ptr wlen` into leading alignment padding `[work_ptr .. +pad)` and the
8-byte-aligned `M6Hdr` workspace `[fullM6WorkBase work_ptr .. +(wlen - pad))`. -/
theorem region_work_to_m6_workBase {work_ptr : BitVec 64} {wlen : Nat} {m : Mem 64}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hm : region work_ptr wlen m) :
    (region work_ptr (fullAlignPad work_ptr) ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr)) m := by
  have heq : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by omega
  exact (congrFun (region_merge_eq heq hfit) m).mpr hm

/-- Collapse leading alignment padding + `FullM6HdrMem c ext s` (`3,456 B` header + arrays) back
to `region work_ptr wlen`. -/
theorem region_work_from_m6_hdrMem {work_ptr : BitVec 64} {wlen : Nat} {c : FullCfg}
    {ext : List (BitVec 64)} {s : FullState} {m : Mem 64}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen) (hfit : wlen ≤ 2 ^ 64)
    (hhdr : c.hdr = fullM6WorkHdr work_ptr)
    (hav : c.avail = wlen - fullAlignPad work_ptr - fullM6ExtBytes)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (region work_ptr (fullAlignPad work_ptr) ⋆ FullM6HdrMem c ext s) m) :
    region work_ptr wlen m := by
  have hreg : (region work_ptr (fullAlignPad work_ptr) ⋆
      region (fullM6WorkBase work_ptr) (wlen - fullAlignPad work_ptr)) m := by
    refine sep_mono_r (fun _ h => ?_) hm
    have hr := fullM6HdrMem_to_region hcfg hext hlen h
    rw [hhdr, m6ExtAddr_fullM6WorkHdr, hav] at hr
    have hsz : fullM6ExtBytes + (wlen - fullAlignPad work_ptr - fullM6ExtBytes) =
        wlen - fullAlignPad work_ptr := by
      unfold fullM6HdrTotalBytes fullM6ExtBytes at *; omega
    rwa [hsz] at hr
  have heq : fullAlignPad work_ptr + (wlen - fullAlignPad work_ptr) = wlen := by omega
  exact (congrFun (region_merge_eq heq hfit) m).mp hreg

theorem unsatDimacsBytes_len : unsatDimacsBytes.length = 12 := by
  decide

theorem unsatDimacsBytes_eq_emit : unsatDimacsBytes = emitDimacsBytes 0 [[]] := by
  decide

theorem parseDimacs_unsatDimacsBytes :
    parseDimacs unsatDimacsBytes = some (kissatCnfToDimacs [[]]) := by
  rw [unsatDimacsBytes_eq_emit]
  exact parseDimacs_emitDimacsBytes (by decide) (by decide) (by decide)

theorem unsatDimacsCnf_unsat : (kissatCnfToDimacs [[]]).Unsat := by
  intro α
  have hce : kissatClauseToDimacs [] = CNF.Clause.empty :=
    CNF.Clause.ext (by simp [kissatClauseToDimacs, CNF.Clause.literals_ofLiterals])
  have heq : kissatCnfToDimacs [[]] = CNF.empty.add CNF.Clause.empty := by
    simp [kissatCnfToDimacs, CNF.empty, CNF.add, hce]
  rw [heq, CNF.eval_add, CNF.eval_empty, CNF.Clause.eval_empty]
  rfl

theorem satEmptyDimacsBytes_len : satEmptyDimacsBytes.length = 10 := by
  decide

theorem satEmptyDimacsBytes_eq_emit : satEmptyDimacsBytes = emitDimacsBytes 0 [] := by
  decide

theorem parseDimacs_satEmptyDimacsBytes :
    parseDimacs satEmptyDimacsBytes = some (kissatCnfToDimacs []) := by
  rw [satEmptyDimacsBytes_eq_emit]
  exact parseDimacs_emitDimacsBytes (by decide) (by decide) (by decide)

theorem satEmptyDimacsCnf_not_unsat : ¬ (kissatCnfToDimacs []).Unsat := by
  intro hu
  have h : kissatCnfToDimacs [] = CNF.empty := by simp [kissatCnfToDimacs, CNF.empty]
  have hev := hu (fun _ => false)
  rw [h, CNF.eval_empty] at hev
  exact Bool.false_ne_true hev.symm

private theorem parseClauseAux_vars_pos :
    ∀ {fuel mv : Nat} {acc : List (Literal Nat)} {bs : List UInt8}
      {cl : CNF.Clause Nat} {rest : List UInt8},
      (∀ l ∈ acc, 1 ≤ l.1) →
      parseClauseAux fuel mv acc bs = some (cl, rest) →
      ∀ l ∈ cl.literals, 1 ≤ l.1
  | 0, _, _, _, _, _, _, h => by cases h
  | fuel + 1, mv, acc, bs, cl, rest, hacc, h => by
    unfold parseClauseAux at h
    cases hs : skipWsComments bs with
    | nil => simp [hs] at h
    | cons b bs' =>
      rw [hs] at h
      split at h
      · next _ heq => cases heq
      · next _ rest1 heq =>
        cases heq
        cases hpn : parseNat bs' with
        | none => rw [hpn] at h; cases h
        | some p =>
          obtain ⟨v, r'⟩ := p
          rw [hpn] at h; dsimp only at h
          rcases hbv : (1 ≤ v && v ≤ mv) with _ | _
          · simp only [hbv, Bool.false_eq_true, ↓reduceIte] at h; cases h
          · simp only [hbv, ↓reduceIte] at h
            refine parseClauseAux_vars_pos (fun l hl => ?_) h
            rcases List.mem_cons.mp hl with rfl | hl'
            · simp only [Bool.and_eq_true, decide_eq_true_eq] at hbv; exact hbv.1
            · exact hacc l hl'
      · next _ b1 rest1 _ heq =>
        cases heq
        cases hpn : parseNat (b :: bs') with
        | none => rw [hpn] at h; cases h
        | some p =>
          obtain ⟨v, r'⟩ := p
          cases v with
          | zero =>
            rw [hpn] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            intro l hl
            rw [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hl
            exact hacc l hl
          | succ v' =>
            rw [hpn] at h
            rcases hbv : (1 ≤ v' + 1 && v' + 1 ≤ mv) with _ | _
            · simp only [hbv, Bool.false_eq_true, ↓reduceIte] at h; cases h
            · simp only [hbv, ↓reduceIte] at h
              refine parseClauseAux_vars_pos (fun l hl => ?_) h
              rcases List.mem_cons.mp hl with rfl | hl'
              · exact Nat.succ_pos v'
              · exact hacc l hl'

private theorem parseClauses_vars_pos {mv : Nat} :
    ∀ {nc : Nat} {acc : CNF Nat} {bs : List UInt8} {cnf : CNF Nat},
      CnfVarsPos acc → parseClauses mv nc acc bs = some cnf → CnfVarsPos cnf
  | 0, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    by_cases he : (skipWsComments bs).isEmpty
    · simp only [he, ↓reduceIte, Option.some.injEq] at h
      exact h ▸ hacc
    · simp [he] at h
  | nc + 1, acc, bs, cnf, hacc, h => by
    unfold parseClauses at h
    cases hc : parseClause mv bs with
    | none => simp [hc] at h
    | some p =>
      rcases p with ⟨cl, bs''⟩
      simp only [hc, Bind.bind, Option.bind_some] at h
      exact parseClauses_vars_pos
        (cnfVarsPos_add hacc (parseClauseAux_vars_pos (fun _ hm => absurd hm List.not_mem_nil) hc))
        h

theorem parseDimacs_vars_pos {bs : List UInt8} {cnf : CNF Nat}
    (h : parseDimacs bs = some cnf) : CnfVarsPos cnf := by
  unfold parseDimacs at h
  cases hh : parseHeader bs with
  | none => simp [hh] at h
  | some hdr =>
    simp only [hh, Bind.bind, Option.bind_some] at h
    exact parseClauses_vars_pos cnfVarsPos_empty h

private theorem emitDimacsHdrBytes_len_pos (mv nc : Nat) :
    0 < (emitDimacsHdrBytes mv nc).length := by
  unfold emitDimacsHdrBytes dimacsHeaderPrefix
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

theorem exportStateBytes_len_pos (k : FullCoreState) :
    0 < (exportStateBytes k).length := by
  unfold exportStateBytes emitDimacsBytes
  simp only [List.length_append]
  exact Nat.lt_of_lt_of_le (emitDimacsHdrBytes_len_pos _ _) (Nat.le_add_right _ _)

theorem exportStateBytes_inconsistent_eq {k : FullCoreState}
    (hinc : k.inconsistent ≠ 0#64) :
    exportStateBytes k = unsatDimacsBytes := by
  unfold exportStateBytes exportStateClauses exportStateMv
  have hL : (if k.inconsistent ≠ 0#64 then [[]] else
      exportTrailUnitClauses k ++ exportBinClauses k ++ exportArenaClauses k) = [[]] :=
    ite_eq_left hinc
  have hM : (if k.inconsistent ≠ 0#64 then 0 else k.cur_vars) = 0 :=
    ite_eq_left hinc
  rw [hL, hM, ← unsatDimacsBytes_eq_emit]

end

/-! ## 2. Separation-Logic `Spec` Contracts (`XPost`-Polymorphic) -/

@[expose] public section

/-- Generic `M6Hdr`-aware preprocessing contract (operating over `FullM6HdrInv` and
`FullM6HdrMem` while permitting M4 compaction via `FullM4Compact.FullCfgCompat`). -/
def fullM6PreprocessSpec : Spec [i64] [i64] :=
  fun (h, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ s.core.cur_level = 0 ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r c' ext' s' m',
        FullCfgCompat c c' → s'.LengthsOk c' →
        FullM6HdrCfgOk c' → M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 20#64 → F0.Unsat) →
        (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
        (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
        (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m'

/-- Strengthened `full_m6_mem_init` specification carrying `probing = 0`,
`vals = replicate`, and `wvec = replicate` needed by `fullParseBodySpec`. -/
def fullM6MemInitExactSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cend, work_base, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_base.toNat + avail.toNat < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' →
        (avail.toNat < fullM6HdrTotalBytes ∨
          ∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
            avail.toNat - fullM6ExtBytes < fullFixedBytes mv + nc * 40 + 136) →
        Q (0#64, ()) m') ∧
      ∀ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (j : Nat)
        (rest : List UInt8) (m' : Mem 64),
        c.hdr = work_base + BitVec.ofNat 64 fullM6ExtBytes →
        c.avail = avail.toNat - fullM6ExtBytes →
        FullM6HdrCfgOk c → M6HdrExtInitOk ext →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        FullM6HdrInv c (shiftDownCnf CNF.empty) ext s →
        s.core.cur_vars = c.mv → s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
        s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
        s.core.oom = 0#64 → s.core.inconsistent = 0#64 → s.core.probing = 0#64 →
        s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
        s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
        (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m' → Q (c.hdr, ()) m'

/-- `XPost`-polymorphic WP contract for
`kissat_emit_trivial_cnf_bytes(out, cap, out_len_ptr, is_unsat)`.
Writes `"p cnf 0 1\n0\n"` (`12 B`, ret `20#64`) if `is_unsat ≠ 0#64`, or `"p cnf 0 0\n"`
(`10 B`, ret `10#64`) otherwise, leaving `buf` intact when `buf.length < want.length`. -/
def kissatEmitTrivialCnfBytesSpec : Spec [i64, i64, i64, i64] [i64] :=
  fun args m Q _ =>
    ∃ (out out_len_ptr old_len is_unsat : BitVec 64) (buf : List UInt8)
      (R : Mem 64 → Prop),
      args = (out, BitVec.ofNat 64 buf.length, out_len_ptr, is_unsat, ()) ∧
      buf.length < 2 ^ 64 ∧
      (bytes out buf ⋆ cell64 out_len_ptr old_len ⋆ R) m ∧
      ∀ (r : BitVec 64) (m' : Mem 64),
        (buf.length <
            (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length →
          r = 0#64 ∧
          (bytes out buf ⋆ cell64 out_len_ptr (BitVec.ofNat 64
            (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length) ⋆
            R) m') →
        ((if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length ≤
            buf.length →
          r = (if is_unsat ≠ 0#64 then (20#64 : BitVec 64) else 10#64) ∧
          (bytes out ((if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes) ++
              buf.drop
                (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length) ⋆
            cell64 out_len_ptr (BitVec.ofNat 64
              (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length) ⋆
            R) m') →
        Q (r, ()) m'

/-- `XPost`-polymorphic WP contract for
`kissat_simplify_export_loaded(h, cnf_end, out)` after `full_m6_mem_init`
(with `out_len = 0#64`). -/
def kissatSimplifyExportLoadedSpec : Spec [i64, i64, i64] [i64] :=
  fun (h, cnf_end, outDesc, ()) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState)
      (cnf_ptr out_ptr : BitVec 64)
      (cnfBytes buf : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
      h = c.hdr ∧
      cnf_end = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      i0 ≤ cnfBytes.length ∧
      parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
      FullM6HdrCfgOk c ∧
      M6HdrExtInitOk ext ∧
      s.core.cur_vars = c.mv ∧
      s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
      s.core.cur_level = 0 ∧
      s.core.trail_end = 0 ∧
      s.core.propagated = 0 ∧
      s.core.arena_len = 0 ∧
      s.core.oom = 0#64 ∧
      s.core.probing = 0#64 ∧
      s.core.inconsistent = 0#64 ∧
      s.core.vals = List.replicate (2 * c.max_vars) 0#8 ∧
      s.core.wvec = List.replicate (4 * c.max_vars) 0#32 ∧
      FullM6HdrInv c (shiftDownCnf CNF.empty) ext s ∧
      outDesc ≠ 0#64 ∧
      (outDesc &&& 7#64) = 0#64 ∧
      outDesc.toNat + 24 < 2 ^ 64 ∧
      buf.length < 2 ^ 64 ∧
      (0 < buf.length → out_ptr ≠ 0#64) ∧
      out_ptr.toNat + buf.length < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
        bytes out_ptr buf ⋆ R) m ∧
      ∀ (r : BitVec 64) (c' : FullCfg) (ext' : List (BitVec 64)) (s' : FullState)
        (outBytes : List UInt8) (written : Nat) (m' : Mem 64),
        FullCfgCompat c c' →
        s'.LengthsOk c' →
        FullM6HdrCfgOk c' →
        M6HdrExtOk ext' →
        (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
        written < 2 ^ 64 →
        (r = 0#64 →
          (written = 0 ∨ buf.length < written) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s' ⋆
            exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
              (BitVec.ofNat 64 written) ⋆ bytes out_ptr buf ⋆ R) m') →
        (r ≠ 0#64 →
          0 < written ∧
          written ≤ buf.length ∧
          outBytes.length = written ∧
          (∃ F0 cnfOut, parseDimacs cnfBytes = some F0 ∧
            parseDimacs outBytes = some cnfOut ∧ (cnfOut.Unsat → F0.Unsat)) ∧
          (r = 20#64 →
            outBytes = unsatDimacsBytes ∧
            ∃ F0, parseDimacs cnfBytes = some F0 ∧ F0.Unsat) ∧
          (r = 10#64 →
            outBytes = satEmptyDimacsBytes ∧
            ∃ F0, parseDimacs cnfBytes = some F0) ∧
          (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s' ⋆
            exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
              (BitVec.ofNat 64 written) ⋆
            bytes out_ptr (outBytes ++ buf.drop written) ⋆ R) m') →
        (UnitUnsatTrace c.mv (List.replicate (2 * c.mv) 0#8) (cnfBytes.drop i0) c.nc →
          12 ≤ buf.length → r = 20#64) →
        Q (r, ()) m'

/-- Top-level `XPost`-polymorphic `Mem 64` WP contract for
`kissat_simplify_export_bytes(cnf_ptr, cnf_len, work_ptr, work_cap, fuel, out)`. -/
def kissatSimplifyExportBytesSpec : Spec [i64, i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cnf_len, work_ptr, work_cap, fuel, outDesc, ()) m Q _ =>
    ∃ (cnfBytes buf : List UInt8) (wlen : Nat) (out_ptr old_len : BitVec 64)
      (R : Mem 64 → Prop),
      cnf_len = BitVec.ofNat 64 cnfBytes.length ∧
      work_cap = BitVec.ofNat 64 wlen ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      work_ptr.toNat + wlen < 2 ^ 64 ∧
      outDesc ≠ 0#64 ∧
      (outDesc &&& 7#64) = 0#64 ∧
      outDesc.toNat + 24 < 2 ^ 64 ∧
      buf.length < 2 ^ 64 ∧
      (0 < buf.length → out_ptr ≠ 0#64) ∧
      out_ptr.toNat + buf.length < 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) old_len ⋆
        bytes out_ptr buf ⋆ R) m ∧
      ∀ (r : BitVec 64) (outBytes : List UInt8) (written : Nat) (m' : Mem 64),
        (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
        written < 2 ^ 64 →
        (r = 0#64 →
          (written = 0 ∨ buf.length < written) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
            exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
              (BitVec.ofNat 64 written) ⋆ bytes out_ptr buf ⋆ R) m') →
        (r ≠ 0#64 →
          0 < written ∧
          written ≤ buf.length ∧
          outBytes.length = written ∧
          (∃ F0 cnfOut, parseDimacs cnfBytes = some F0 ∧
            parseDimacs outBytes = some cnfOut ∧ (cnfOut.Unsat → F0.Unsat)) ∧
          (r = 20#64 →
            outBytes = unsatDimacsBytes ∧
            ∃ F0, parseDimacs cnfBytes = some F0 ∧ F0.Unsat) ∧
          (r = 10#64 →
            outBytes = satEmptyDimacsBytes ∧
            ∃ F0, parseDimacs cnfBytes = some F0) ∧
          (bytes cnf_ptr cnfBytes ⋆ region work_ptr wlen ⋆
            exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
              (BitVec.ofNat 64 written) ⋆
            bytes out_ptr (outBytes ++ buf.drop written) ⋆ R) m') →
        (∀ mv nc i0,
          cnf_ptr ≠ 0#64 → work_ptr ≠ 0#64 → 0 < fuel.toNat →
          fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen →
          fullAlignPad work_ptr + fullM6ExtBytes + fullFixedBytes mv + nc * 40 + 136 ≤ wlen →
          i0 ≤ cnfBytes.length →
          parseHeader cnfBytes = some (mv, nc, cnfBytes.drop i0) →
          UnitUnsatTrace mv (List.replicate (2 * mv) 0#8) (cnfBytes.drop i0) nc →
          12 ≤ buf.length → r = 20#64) →
        Q (r, ()) m'

/-- Specification slice covering only the three `ExportCnfEntry` C0 functions. -/
def exportCnfEntryOnlyEnv : Env :=
  fun f as rs =>
    if h : f = "kissat_emit_trivial_cnf_bytes" ∧
        as = [i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatEmitTrivialCnfBytesSpec
    else if h : f = "kissat_simplify_export_loaded" ∧
        as = [i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatSimplifyExportLoadedSpec
    else if h : f = "kissat_simplify_export_bytes" ∧
        as = [i64, i64, i64, i64, i64, i64] ∧ rs = [i64] then
      h.2.1 ▸ h.2.2 ▸ kissatSimplifyExportBytesSpec
    else
      fun _ _ _ _ => False

def specCast {as as' rs rs' : List Ty} (ha : as = as') (hr : rs = rs')
    (S : Spec as' rs') : Spec as rs :=
  @Eq.rec _ as' (fun x _ => Spec x rs)
    (@Eq.rec _ rs' (fun y _ => Spec as' y) S rs hr.symm) as ha.symm

/-- Standalone closed specification environment for `exportCnfEntryMod` (`12` C0 functions +
`4` Kissat M6 extern contracts). -/
def exportCnfEntryEnv : Env :=
  fun f as rs xs m Q X =>
    exportCnfEntryOnlyEnv f as rs xs m Q X ∨
    (∃ h : f = "full_m6_mem_init" ∧ as = [i64, i64, i64, i64, i64] ∧ rs = [i64],
      specCast h.2.1 h.2.2 fullM6MemInitExactSpec xs m Q X) ∨
    (∃ h : f = "full_parse_body_m6" ∧ as = [i64, i64] ∧ rs = [i64],
      specCast h.2.1 h.2.2 fullParseBodySpec xs m Q X) ∨
    (∃ h : f = "full_preprocess_m6" ∧ as = [i64] ∧ rs = [i64],
      specCast h.2.1 h.2.2 fullM6PreprocessSpec xs m Q X) ∨
    exportCnfStateEnv f as rs xs m Q X

end

public section

theorem fullM6PreprocessSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r c' ext' s' m',
      FullCfgCompat c c' → s'.LengthsOk c' →
      FullM6HdrCfgOk c' → M6HdrExtOk ext' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 1#64 → FullM6HdrInv c' F0 ext' s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c'.extend_cap) →
      (FullM6HdrMem c' ext' s' ⋆ R) m' → Q (r, ()) m') :
    fullM6PreprocessSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hcl0, hm, hQ⟩

theorem fullM6PreprocessSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : fullM6PreprocessSpec xs m Q X) :
    fullM6PreprocessSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem fullM6MemInitExactSpec_of {cnf_ptr cend work_base avail fuel : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hcend : cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hcfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hwfit : work_base.toNat + avail.toNat < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m)
    (hfail : ∀ m', (bytes cnf_ptr cnfBytes ⋆ region work_base avail.toNat ⋆ R) m' →
      (avail.toNat < fullM6HdrTotalBytes ∨
        ∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat - fullM6ExtBytes < fullFixedBytes mv + nc * 40 + 136) →
      Q (0#64, ()) m')
    (hok : ∀ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (j : Nat)
      (rest : List UInt8) (m' : Mem 64),
      c.hdr = work_base + BitVec.ofNat 64 fullM6ExtBytes →
      c.avail = avail.toNat - fullM6ExtBytes →
      FullM6HdrCfgOk c → M6HdrExtInitOk ext →
      parseHeader cnfBytes = some (c.mv, c.nc, rest) →
      j ≤ cnfBytes.length → cnfBytes.drop j = rest →
      FullM6HdrInv c (shiftDownCnf CNF.empty) ext s →
      s.core.cur_vars = c.mv → s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
      s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
      s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
      s.core.oom = 0#64 → s.core.inconsistent = 0#64 → s.core.probing = 0#64 →
      s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
      s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
      (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ R) m' → Q (c.hdr, ()) m') :
    fullM6MemInitExactSpec (cnf_ptr, cend, work_base, avail, fuel, ()) m Q X :=
  ⟨cnfBytes, R, hcend, hcfit, hwfit, hm, hfail, hok⟩

theorem fullM6MemInitExactSpec_monoX
    {xs : Tup Val [i64, i64, i64, i64, i64]} {m : Mem 64} {Q : Post [i64]} {X X' : XPost}
    (h : fullM6MemInitExactSpec xs m Q X) : fullM6MemInitExactSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, _, _, ⟨⟩⟩; exact h

/-! ## 3. BitVec Helpers, Parser Bridges, & Sub-Function WP Proofs -/

private theorem ref_isDimacsWs_eq (b : UInt8) :
    Ref.isDimacsWs b = LratBytes.isDimacsWs b := rfl

private theorem ref_isDimacsDigit_eq (b : UInt8) :
    Ref.isDimacsDigit b = LratBytes.isDimacsDigit b := rfl

private theorem ref_dimacsBound_eq : Ref.dimacsBound = LratBytes.dimacsBound := rfl

private theorem ref_skipWsCommentsAux_eq (inC : Bool) (bs : List UInt8) :
    Ref.skipWsCommentsAux inC bs = LratBytes.skipWsCommentsAux inC bs := by
  induction bs generalizing inC with
  | nil => cases inC <;> rfl
  | cons b bs ih =>
    cases inC
    · by_cases hw : LratBytes.isDimacsWs b
      · simp [Ref.skipWsCommentsAux, LratBytes.skipWsCommentsAux, ref_isDimacsWs_eq, hw, ih]
      · by_cases hc : b == 99 <;>
          simp [Ref.skipWsCommentsAux, LratBytes.skipWsCommentsAux, ref_isDimacsWs_eq, hw, hc, ih]
    · by_cases h10 : b = 10
      · subst h10; simp [Ref.skipWsCommentsAux, LratBytes.skipWsCommentsAux, ih false]
      · rw [Ref.skipWsCommentsAux.eq_3, LratBytes.skipWsCommentsAux.eq_3] <;>
          first | exact ih true | exact h10

private theorem ref_skipWsComments_eq (bs : List UInt8) :
    Ref.skipWsComments bs = LratBytes.skipWsComments bs :=
  ref_skipWsCommentsAux_eq false bs

private theorem ref_skipWs_eq (bs : List UInt8) :
    Ref.skipWs bs = LratBytes.skipWs bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    by_cases hw : LratBytes.isDimacsWs b <;>
      simp [Ref.skipWs, LratBytes.skipWs, ref_isDimacsWs_eq, hw, ih]

private theorem ref_skipWs1_eq (bs : List UInt8) :
    Ref.skipWs1 bs = LratBytes.skipWs1 bs := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    simp only [Ref.skipWs1, LratBytes.skipWs1, ref_isDimacsWs_eq, ref_skipWs_eq]

private theorem ref_parseDigitsAux_eq (acc : Nat) (bs : List UInt8) :
    Ref.parseDigitsAux acc bs = LratBytes.parseDigitsAux acc bs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    by_cases hd : LratBytes.isDimacsDigit b
    · by_cases hlt : acc * 10 + (b.toNat - 48) < LratBytes.dimacsBound <;>
        simp [Ref.parseDigitsAux, LratBytes.parseDigitsAux,
          ref_isDimacsDigit_eq, ref_dimacsBound_eq, hd, hlt, ih]
    · by_cases hw : LratBytes.isDimacsWs b <;>
        simp [Ref.parseDigitsAux, LratBytes.parseDigitsAux,
          ref_isDimacsDigit_eq, ref_isDimacsWs_eq, hd, hw]

private theorem ref_parseNat_eq (bs : List UInt8) :
    Ref.parseNat bs = LratBytes.parseNat bs := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    simp only [Ref.parseNat, LratBytes.parseNat, ref_isDimacsDigit_eq, ref_parseDigitsAux_eq]

private theorem ref_parseHeader_eq_lrat (bs : List UInt8) :
    Ref.parseHeader bs = LratBytes.parseHeader bs := by
  simp only [Ref.parseHeader, LratBytes.parseHeader,
    ref_skipWsComments_eq, ref_skipWs1_eq, ref_parseNat_eq]
  rfl

private theorem ref_parseClauseAux_eq (fuel mv : Nat)
    (acc : List (Literal Nat)) (bs : List UInt8) :
    Ref.parseClauseAux fuel mv acc bs = LratBytes.parseClauseAux fuel mv acc bs := by
  induction fuel generalizing acc bs with
  | zero => rfl
  | succ fuel ih =>
    simp only [Ref.parseClauseAux, LratBytes.parseClauseAux,
      ref_skipWsComments_eq, ref_parseNat_eq, ih]
    rfl

private theorem ref_parseClause_eq (mv : Nat) (bs : List UInt8) :
    Ref.parseClause mv bs = LratBytes.parseClause mv bs :=
  ref_parseClauseAux_eq (bs.length + 1) mv [] bs

private theorem ref_parseClauses_eq (mv nc : Nat) (cnf : CNF Nat) (bs : List UInt8) :
    Ref.parseClauses mv nc cnf bs = LratBytes.parseClauses mv nc cnf bs := by
  induction nc generalizing cnf bs with
  | zero => simp only [Ref.parseClauses, LratBytes.parseClauses, ref_skipWsComments_eq]
  | succ k ih => simp only [Ref.parseClauses, LratBytes.parseClauses, ref_parseClause_eq, ih]

private theorem ref_parseDimacs_eq_lrat (bs : List UInt8) :
    Ref.parseDimacs bs = LratBytes.parseDimacs bs := by
  simp only [Ref.parseDimacs, LratBytes.parseDimacs, ref_parseHeader_eq_lrat]
  cases LratBytes.parseHeader bs with
  | none => rfl
  | some hdr => exact ref_parseClauses_eq _ _ _ _

theorem bv64_ofNat_lt_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a < BitVec.ofNat 64 b) = true ↔ a < b := by
  simp [BitVec.lt_def, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv64_ofNat_le_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a ≤ BitVec.ofNat 64 b) = true ↔ a ≤ b := by
  simp [BitVec.le_def, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem bv64_sub_of_le {a b : Nat} (ha : a < 2 ^ 64) (hba : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega)]
        exact hba),
    BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

theorem bv64_allOnes_sub (x : BitVec 64) :
    BitVec.allOnes 64 - x = BitVec.ofNat 64 (2 ^ 64 - 1 - x.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_allOnes]; omega),
    BitVec.toNat_allOnes, bv64_ofNat_toNat (by omega)]

theorem bv64_alignPad (p : BitVec 64) :
    ((8#64 - (p &&& 7#64)) &&& 7#64) = BitVec.ofNat 64 (fullAlignPad p) := by
  apply BitVec.eq_of_toNat_eq
  rw [fullAlignPad_eq, bv64_ofNat_toNat (by have := fullAlignPad_lt8 p; omega)]

/-- WP correctness of `kissat_emit_trivial_cnf_bytes(out, cap, out_len_ptr, is_unsat)`. -/
theorem kissat_emit_trivial_cnf_bytes_wp (Γ : Env)
    (hByte : ∀ a m Q X, kissatEmitByteSpec a m Q X →
      Γ "kissat_emit_byte" [i64, i64, i64, i64] [i64] a m Q X)
    (hHdr : ∀ a m Q X, kissatEmitDimacsHdrSpec a m Q X →
      Γ "kissat_emit_dimacs_hdr" [i64, i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, kissatEmitTrivialCnfBytesSpec args m Q X →
      Func.wp Γ kissat_emit_trivial_cnf_bytes_body args m Q X := by
  rintro args m Q X ⟨out, out_len_ptr, old_len, is_unsat, buf, R, rfl, hcap, hm, hQ⟩
  unfold Func.wp kissat_emit_trivial_cnf_bytes_body; dsimp only
  c0_hsteps_nogrp
  · have hne : is_unsat ≠ 0#64 := ‹_›
    have hwant : (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes) =
        unsatDimacsBytes := ite_eq_left hne
    have hcode : (if is_unsat ≠ 0#64 then (20#64 : BitVec 64) else 10#64) = 20#64 :=
      ite_eq_left hne
    have hQ' := hQ
    rw [hwant, hcode, unsatDimacsBytes_len] at hQ'
    refine wp_store_sep
      (store_cell64 (a := out_len_ptr) (R := bytes out buf ⋆ R) 12#64 (sep_ac hm))
      fun m1 hm1 => ?_
    c0_hsteps_nogrp
    · have hlt : buf.length < 12 :=
        (bv64_ofNat_lt_iff hcap (by decide)).mp (by simpa using ‹_›)
      exact hQ' 0#64 m1 (fun _ => ⟨rfl, sep_ac hm1⟩) (fun hge => absurd hlt (by omega))
    · have hge : 12 ≤ buf.length := by
        have hnc : ¬ buf.length % 2 ^ 64 < BitVec.toNat (12 : BitVec 64) := ‹_›
        rw [Nat.mod_eq_of_lt hcap, show BitVec.toNat (12 : BitVec 64) = 12 by decide] at hnc
        exact Nat.le_of_not_lt hnc
      c0_call hHdr
      refine ⟨out, buf, 0, 0#64, 1#64, cell64 out_len_ptr 12#64 ⋆ R, rfl, hcap,
        by decide, sep_ac hm1, fun m2 _ hm2 => ?_⟩
      rw [show BitVec.toNat (0#64 : BitVec 64) = 0 by decide,
          show BitVec.toNat (1#64 : BitVec 64) = 1 by decide] at hm2
      c0_call hByte
      refine ⟨out, writeSlice buf 0 (emitDimacsHdrBytes 0 1), 10, 48#64,
        cell64 out_len_ptr 12#64 ⋆ R,
        by rw [writeSlice_length, Nat.zero_add,
          show (emitDimacsHdrBytes 0 1).length = 10 by decide]; rfl,
        by rw [writeSlice_length]; exact hcap, by decide, sep_ac hm2, fun m3 _ hm3 => ?_⟩
      rw [show BitVec.toNat (48#64 : BitVec 64) = 48 by decide] at hm3
      c0_call hByte
      refine ⟨out,
        writeSlice (writeSlice buf 0 (emitDimacsHdrBytes 0 1)) 10 [UInt8.ofNat 48],
        11, 10#64, cell64 out_len_ptr 12#64 ⋆ R,
        by simp only [writeSlice_length]; rfl,
        by simp only [writeSlice_length]; exact hcap, by decide, sep_ac hm3, fun m4 _ hm4 => ?_⟩
      have hws1 : writeSlice (writeSlice (writeSlice buf 0 (emitDimacsHdrBytes 0 1)) 10 [48])
          11 [10] = unsatDimacsBytes ++ buf.drop 12 := by
        rw [show (10 : Nat) = 0 + (emitDimacsHdrBytes 0 1).length by decide,
          ← writeSlice_append,
          show (11 : Nat) = 0 + (emitDimacsHdrBytes 0 1 ++ [48]).length by decide,
          ← writeSlice_append]
        have hfit := writeSlice_fit buf 0 unsatDimacsBytes (by rw [unsatDimacsBytes_len]; omega)
        rw [unsatDimacsBytes_len] at hfit
        simpa [unsatDimacsBytes, asciiZero, asciiNewline, List.append_assoc] using hfit
      rw [show UInt8.ofNat (BitVec.toNat (10#64 : BitVec 64)) = 10 by decide,
          show UInt8.ofNat 48 = 48 by decide, hws1] at hm4
      rw [show (11 + 1 : Nat) = 12 by decide]
      refine wp_store_sep
        (store_cell64 (a := out_len_ptr)
          (R := bytes out (unsatDimacsBytes ++ buf.drop 12) ⋆ R) 12#64 (sep_ac hm4))
        fun m5 hm5 => ?_
      c0_hsteps_nogrp
      exact hQ' 20#64 m5 (fun hlt => absurd hge (by omega)) (fun _ => ⟨rfl, sep_ac hm5⟩)
  · have hze : is_unsat = 0#64 := ‹_›
    have hwant : (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes) =
        satEmptyDimacsBytes := ite_eq_right (fun h => absurd hze h)
    have hcode : (if is_unsat ≠ 0#64 then (20#64 : BitVec 64) else 10#64) = 10#64 :=
      ite_eq_right (fun h => absurd hze h)
    have hQ' := hQ
    rw [hwant, hcode, satEmptyDimacsBytes_len] at hQ'
    refine wp_store_sep
      (store_cell64 (a := out_len_ptr) (R := bytes out buf ⋆ R) 10#64 (sep_ac hm))
      fun m1 hm1 => ?_
    c0_hsteps_nogrp
    · have hlt : buf.length < 10 :=
        (bv64_ofNat_lt_iff hcap (by decide)).mp (by simpa using ‹_›)
      exact hQ' 0#64 m1 (fun _ => ⟨rfl, sep_ac hm1⟩) (fun hge => absurd hlt (by omega))
    · have hge : 10 ≤ buf.length := by
        have hnc : ¬ buf.length % 2 ^ 64 < BitVec.toNat (10 : BitVec 64) := ‹_›
        rw [Nat.mod_eq_of_lt hcap, show BitVec.toNat (10 : BitVec 64) = 10 by decide] at hnc
        exact Nat.le_of_not_lt hnc
      c0_call hHdr
      refine ⟨out, buf, 0, 0#64, 0#64, cell64 out_len_ptr 10#64 ⋆ R, rfl, hcap,
        by decide, sep_ac hm1, fun m2 _ hm2 => ?_⟩
      have hws : writeSlice buf 0 (emitDimacsHdrBytes 0 0) =
          satEmptyDimacsBytes ++ buf.drop 10 := by
        have hfit := writeSlice_fit buf 0 satEmptyDimacsBytes
          (by rw [satEmptyDimacsBytes_len]; omega)
        rw [satEmptyDimacsBytes_len] at hfit
        simpa [satEmptyDimacsBytes] using hfit
      rw [show (0#64 : BitVec 64).toNat = 0 by decide] at hm2 ⊢
      rw [hws] at hm2
      rw [Nat.zero_add, show (emitDimacsHdrBytes 0 0).length = 10 by decide]
      refine wp_store_sep
        (store_cell64 (a := out_len_ptr)
          (R := bytes out (satEmptyDimacsBytes ++ buf.drop 10) ⋆ R) 10#64 (sep_ac hm2))
        fun m3 hm3 => ?_
      c0_hsteps_nogrp
      exact hQ' 10#64 m3 (fun hlt => absurd hge (by omega)) (fun _ => ⟨rfl, sep_ac hm3⟩)

private theorem call_emit_triv {Γ : Env}
    (hTriv : ∀ a m Q X, kissatEmitTrivialCnfBytesSpec a m Q X →
      Γ "kissat_emit_trivial_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X)
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {cnf_ptr outDesc out_ptr old_len is_unsat : BitVec 64}
    {cnfBytes buf : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcap : buf.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
      exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) old_len ⋆
      bytes out_ptr buf ⋆ R) m)
    (hk : ∀ r m',
      (buf.length <
          (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length →
        r = 0#64 ∧
        (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
          exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) (BitVec.ofNat 64
            (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length) ⋆
          bytes out_ptr buf ⋆ R) m') →
      ((if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length ≤ buf.length →
        r = (if is_unsat ≠ 0#64 then (20#64 : BitVec 64) else 10#64) ∧
        (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆
          exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) (BitVec.ofNat 64
            (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length) ⋆
          bytes out_ptr ((if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes) ++
            buf.drop (if is_unsat ≠ 0#64 then unsatDimacsBytes else satEmptyDimacsBytes).length) ⋆
          R) m') →
      Q (r, ()) m') :
    wp Γ Q X (.call (as := [i64, i64, i64, i64]) (bs := [i64])
      "kissat_emit_trivial_cnf_bytes"
      (Arg.var out_ptr, Arg.var (BitVec.ofNat 64 buf.length),
        Arg.var (outDesc + 16#64), Arg.imm is_unsat, ())
      fun p => Expr.ret (Arg.var p.fst, ())) m := by
  c0_call hTriv
  refine ⟨out_ptr, outDesc + 16#64, old_len, is_unsat, buf,
    bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s ⋆ cell64 outDesc out_ptr ⋆
      cell64 (outDesc + 8#64) (BitVec.ofNat 64 buf.length) ⋆ R,
    rfl, hcap, by unfold exportOutMem at hm; exact sep_ac hm, fun r m' h0 h1 => ?_⟩
  c0_hsteps_nogrp
  exact hk r m'
    (fun hlt => ⟨(h0 hlt).1, by unfold exportOutMem; exact sep_ac (h0 hlt).2⟩)
    (fun hle => ⟨(h1 hle).1, by unfold exportOutMem; exact sep_ac (h1 hle).2⟩)

/-- WP correctness of `kissat_simplify_export_loaded(h, cnf_end, out)`. -/
theorem kissat_simplify_export_loaded_wp (Γ : Env)
    (hParse : ∀ a m Q X, fullParseBodySpec a m Q X →
      Γ "full_parse_body_m6" [i64, i64] [i64] a m Q X)
    (hPre : ∀ a m Q X, fullM6PreprocessSpec a m Q X →
      Γ "full_preprocess_m6" [i64] [i64] a m Q X)
    (hTriv : ∀ a m Q X, kissatEmitTrivialCnfBytesSpec a m Q X →
      Γ "kissat_emit_trivial_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X)
    (hExp : ∀ a m Q X, kissatExportCnfBytesSpec a m Q X →
      Γ "kissat_export_cnf_bytes" [i64, i64, i64, i64] [i64] a m Q X) :
    ∀ args m Q X, kissatSimplifyExportLoadedSpec args m Q X →
      Func.wp Γ kissat_simplify_export_loaded_body args m Q X := by
  rintro ⟨h, cnf_end, outDesc, ⟨⟩⟩ m Q X hs
  obtain ⟨c, ext, s, cnf_ptr, out_ptr, cnfBytes, buf, i0, R,
    rfl, rfl, hcfit, hi0_le, hph, hcfg, hext_init, hcv, hdcur, hcl0, hte0, hprop0,
    hal0, hoom0, hprb0, hinc0, hvals0, hwvec0, hinv0, hout_ne, hout_al, hout_fit,
    hcap, hout_nz, hout_fit2, hm, hQ⟩ := hs
  have hext0 : M6HdrExtOk ext := hext_init.toOk
  unfold Func.wp kissat_simplify_export_loaded_body; dsimp only
  have hm_f : (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆
      (array64 (c.hdr - 2304) ext ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
        bytes out_ptr buf ⋆ R)) m := by
    have hm1 : (FullM6HdrMem c ext s ⋆ (bytes cnf_ptr cnfBytes ⋆
        exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
        bytes out_ptr buf ⋆ R)) m := sep_ac hm
    rw [fullM6HdrMem_iff] at hm1; exact sep_ac hm1
  c0_call hParse
  refine ⟨c, s, cnf_ptr, cnfBytes, i0,
    array64 (c.hdr - 2304) ext ⋆
      exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
      bytes out_ptr buf ⋆ R,
    rfl, rfl, hcfit, hi0_le, (ref_parseHeader_eq_lrat cnfBytes).trans hph, hcv, hdcur, hcl0, hte0,
    hprop0, hal0, hoom0, hprb0, hinc0,
    hvals0, hwvec0, hinv0.sparse, hm_f, fun pb s1 m1 hlen1 hpb _ _ _ h20 h1 hut hm1 => ?_⟩
  have hm1_m6 : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s1 ⋆
      exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
      bytes out_ptr buf ⋆ R) m1 := by
    have htmp : (FullMem c s1 ⋆ (array64 (c.hdr - 2304) ext ⋆
        (bytes cnf_ptr cnfBytes ⋆
          exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
          bytes out_ptr buf ⋆ R))) m1 := sep_ac hm1
    rw [← fullM6HdrMem_iff] at htmp; exact sep_ac htmp
  c0_hsteps_nogrp
  · have hpz : pb = 0#64 := ‹_›; subst hpz
    have hnot_ut : ¬ UnitUnsatTrace c.mv (List.replicate (2 * c.mv) 0#8)
        (cnfBytes.drop i0) c.nc := fun hu => by
      have hmv_le := hinv0.sparse.1.lengths.core_ok.cur_vars_le
      have hvals_take : s.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
        rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
      exact absurd (hut (hvals_take ▸ hu)) (by decide)
    exact hQ 0#64 c ext s1 [] 0 m1 (FullCfgCompat.refl c) hlen1 hcfg hext0
      (Or.inl rfl) (by decide) (fun _ => ⟨Or.inl rfl, hm1_m6⟩) (fun h => absurd rfl h)
      (fun hu _ => absurd hu hnot_ut)
  · have hp_nz : pb ≠ 0#64 := ‹_›
    have hpb_cases : pb = 1#64 ∨ pb = 20#64 := by
      rcases hpb with rfl | rfl | rfl
      · exact absurd rfl hp_nz
      · exact Or.inl rfl
      · exact Or.inr rfl
    have hld_ptr : loadVal m1 i64 outDesc = some out_ptr := by
      refine loadVal_cell64 (R := bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s1 ⋆
        cell64 (outDesc + 8#64) (BitVec.ofNat 64 buf.length) ⋆
        cell64 (outDesc + 16#64) 0#64 ⋆ bytes out_ptr buf ⋆ R) ?_
      unfold exportOutMem at hm1_m6; exact sep_ac hm1_m6
    have hld_cap : loadVal m1 i64 (outDesc + 8#64) = some (BitVec.ofNat 64 buf.length) := by
      refine loadVal_cell64 (R := bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c ext s1 ⋆
        cell64 outDesc out_ptr ⋆ cell64 (outDesc + 16#64) 0#64 ⋆
        bytes out_ptr buf ⋆ R) ?_
      unfold exportOutMem at hm1_m6; exact sep_ac hm1_m6
    refine wp_load_of hld_ptr ?_
    refine wp_load_of hld_cap ?_
    c0_hsteps_nogrp
    · obtain ⟨F0, hparse0, hunsat0⟩ := h20 ‹pb = 20#64›
      rw [ref_parseDimacs_eq_lrat] at hparse0
      dsimp only
      refine call_emit_triv hTriv hcap hm1_m6 fun r m2 h0 h1 => ?_
      have hne1 : (1#64 : BitVec 64) ≠ 0#64 := by decide
      by_cases hlt12 : buf.length < 12
      · obtain ⟨rfl, hm2'⟩ := h0 (by simpa [hne1, unsatDimacsBytes_len] using hlt12)
        exact hQ 0#64 c ext s1 [] 12 m2 (FullCfgCompat.refl c) hlen1 hcfg hext0
          (Or.inl rfl) (by decide)
          (fun _ => ⟨Or.inr hlt12, by simpa [hne1, unsatDimacsBytes_len] using hm2'⟩)
          (fun h => absurd rfl h) (fun _ hge12 => absurd hlt12 (by omega))
      · have hge12 : 12 ≤ buf.length := Nat.le_of_not_lt hlt12
        obtain ⟨rfl, hm2'⟩ := h1 (by simpa [hne1, unsatDimacsBytes_len] using hge12)
        exact hQ 20#64 c ext s1 unsatDimacsBytes 12 m2 (FullCfgCompat.refl c)
          hlen1 hcfg hext0 (Or.inr (Or.inr (Or.inr rfl))) (by decide)
          (fun h => absurd h (by decide))
          (fun _ => ⟨by decide, hge12, unsatDimacsBytes_len,
            ⟨F0, kissatCnfToDimacs [[]], hparse0, parseDimacs_unsatDimacsBytes,
              fun _ => hunsat0⟩,
            fun _ => ⟨rfl, F0, hparse0, hunsat0⟩, fun h => absurd h (by decide),
            by simpa [hne1, unsatDimacsBytes_len] using hm2'⟩)
          (fun _ _ => rfl)
    · have hp1 : pb = 1#64 := hpb_cases.elim id (fun h20 => absurd h20 ‹pb ≠ 20#64›)
      obtain ⟨cnfIn, hparse_in, hsp1, hcl1⟩ := h1 hp1
      rw [ref_parseDimacs_eq_lrat] at hparse_in
      have hcnf_pos : CnfVarsPos cnfIn := parseDimacs_vars_pos hparse_in
      have hnot_ut : ¬ UnitUnsatTrace c.mv (List.replicate (2 * c.mv) 0#8)
          (cnfBytes.drop i0) c.nc := fun hu => by
        have hmv_le := hinv0.sparse.1.lengths.core_ok.cur_vars_le
        have hvals_take : s.core.vals.take (2 * c.mv) = List.replicate (2 * c.mv) 0#8 := by
          rw [hvals0, List.take_replicate, Nat.min_eq_left (by omega)]
        have h20 := hut (hvals_take ▸ hu); rw [hp1] at h20; cases h20
      have hm1_pre : (FullM6HdrMem c ext s1 ⋆ (bytes cnf_ptr cnfBytes ⋆
          exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
          bytes out_ptr buf ⋆ R)) m1 := sep_ac hm1_m6
      c0_call hPre
      refine fullM6PreprocessSpec_of (FullM6HdrInv.mk_inv hcfg hext0 hsp1) hcl1 hm1_pre
        fun pp c' ext' s' m2 hcmp2 hlen2 hcfg2 hext2 hpp _ h20p h1p _ hm2 => ?_
      have hm2_n : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s' ⋆
          exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
          bytes out_ptr buf ⋆ R) m2 := sep_ac hm2
      c0_hsteps_nogrp
      · have hunsat0 : cnfIn.Unsat := shiftDownCnf_unsat hcnf_pos (h20p ‹_›)
        dsimp only
        refine call_emit_triv hTriv hcap hm2_n fun r m3 h0 h1 => ?_
        have hne1 : (1#64 : BitVec 64) ≠ 0#64 := by decide
        by_cases hlt12 : buf.length < 12
        · obtain ⟨rfl, hm3'⟩ := h0 (by simpa [hne1, unsatDimacsBytes_len] using hlt12)
          exact hQ 0#64 c' ext' s' [] 12 m3 hcmp2 hlen2 hcfg2 hext2
            (Or.inl rfl) (by decide)
            (fun _ => ⟨Or.inr hlt12, by simpa [hne1, unsatDimacsBytes_len] using hm3'⟩)
            (fun h => absurd rfl h) (fun hu _ => absurd hu hnot_ut)
        · have hge12 : 12 ≤ buf.length := Nat.le_of_not_lt hlt12
          obtain ⟨rfl, hm3'⟩ := h1 (by simpa [hne1, unsatDimacsBytes_len] using hge12)
          exact hQ 20#64 c' ext' s' unsatDimacsBytes 12 m3 hcmp2 hlen2 hcfg2 hext2
            (Or.inr (Or.inr (Or.inr rfl))) (by decide)
            (fun h => absurd h (by decide))
            (fun _ => ⟨by decide, hge12, unsatDimacsBytes_len,
              ⟨cnfIn, kissatCnfToDimacs [[]], hparse_in, parseDimacs_unsatDimacsBytes,
                fun _ => hunsat0⟩,
              fun _ => ⟨rfl, cnfIn, hparse_in, hunsat0⟩, fun h => absurd h (by decide),
              by simpa [hne1, unsatDimacsBytes_len] using hm3'⟩)
            (fun _ _ => rfl)
      · dsimp only
        refine call_emit_triv hTriv hcap hm2_n fun r m3 h0 h1 => ?_
        have hze0 : ¬ ((0#64 : BitVec 64) ≠ 0#64) := fun h => h rfl
        by_cases hlt10 : buf.length < 10
        · obtain ⟨rfl, hm3'⟩ := h0 (by simpa [hze0, satEmptyDimacsBytes_len] using hlt10)
          exact hQ 0#64 c' ext' s' [] 10 m3 hcmp2 hlen2 hcfg2 hext2
            (Or.inl rfl) (by decide)
            (fun _ => ⟨Or.inr hlt10, by simpa [hze0, satEmptyDimacsBytes_len] using hm3'⟩)
            (fun h => absurd rfl h) (fun hu _ => absurd hu hnot_ut)
        · have hge10 : 10 ≤ buf.length := Nat.le_of_not_lt hlt10
          obtain ⟨rfl, hm3'⟩ := h1 (by simpa [hze0, satEmptyDimacsBytes_len] using hge10)
          exact hQ 10#64 c' ext' s' satEmptyDimacsBytes 10 m3 hcmp2 hlen2 hcfg2 hext2
            (Or.inr (Or.inr (Or.inl rfl))) (by decide)
            (fun h => absurd h (by decide))
            (fun _ => ⟨by decide, hge10, satEmptyDimacsBytes_len,
              ⟨cnfIn, kissatCnfToDimacs [], hparse_in, parseDimacs_satEmptyDimacsBytes,
                fun hu => absurd hu satEmptyDimacsCnf_not_unsat⟩,
              fun h => absurd h (by decide), fun _ => ⟨rfl, cnfIn, hparse_in⟩,
              by simpa [hze0, satEmptyDimacsBytes_len] using hm3'⟩)
            (fun hu _ => absurd hu hnot_ut)
      · exact hQ 0#64 c' ext' s' [] 0 m2 hcmp2 hlen2 hcfg2 hext2
          (Or.inl rfl) (by decide) (fun _ => ⟨Or.inl rfl, hm2_n⟩) (fun h => absurd rfl h)
          (fun hu _ => absurd hu hnot_ut)
      · have ⟨hinv2, _⟩ := h1p ‹pp = 1#64›
        obtain ⟨F_cur2, hw2⟩ := hinv2.sparse.1.witness
        have hm2_exp : (FullMem c' s' ⋆ bytes out_ptr buf ⋆ cell64 (outDesc + 16#64) 0#64 ⋆
            (bytes cnf_ptr cnfBytes ⋆ array64 (c'.hdr - 2304) ext' ⋆
              cell64 outDesc out_ptr ⋆ cell64 (outDesc + 8#64) (BitVec.ofNat 64 buf.length) ⋆
              R)) m2 := by
          have htmp : (FullM6HdrMem c' ext' s' ⋆ (bytes cnf_ptr cnfBytes ⋆
              exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
              bytes out_ptr buf ⋆ R)) m2 := sep_ac hm2_n
          rw [fullM6HdrMem_iff] at htmp
          unfold exportOutMem at htmp; exact sep_ac htmp
        c0_call hExp
        refine ⟨c', shiftDownCnf cnfIn, F_cur2, s', out_ptr, outDesc + 16#64, 0#64, buf,
          bytes cnf_ptr cnfBytes ⋆ array64 (c'.hdr - 2304) ext' ⋆
            cell64 outDesc out_ptr ⋆ cell64 (outDesc + 8#64) (BitVec.ofNat 64 buf.length) ⋆ R,
          by rw [hcmp2.hdr]; rfl, hcap, hlen2, hw2, hm2_exp,
          fun ok s3 outBytes written m3 hlen3 hw3 hl03 _ hinc3 _ _ _ _ _ _ _ hok hwr_lt
            hok0 hok1 => ?_⟩
        c0_hsteps_nogrp
        · obtain rfl := ‹ok = 0#64›
          obtain ⟨_, _, hm3⟩ := hok0 rfl
          have hld_len : loadVal m3 i64 (outDesc + 16#64) = some (BitVec.ofNat 64 written) :=
            loadVal_cell64 (R := FullMem c' s3 ⋆ bytes out_ptr buf ⋆ bytes cnf_ptr cnfBytes ⋆
              array64 (c'.hdr - 2304) ext' ⋆ cell64 outDesc out_ptr ⋆
              cell64 (outDesc + 8#64) (BitVec.ofNat 64 buf.length) ⋆ R) (sep_ac hm3)
          refine wp_join_group (ts := [])
            (fun _ m' => ∃ out_len' : Nat, out_len' < 2 ^ 64 ∧
              (out_len' = 0 ∨ buf.length < out_len') ∧
              (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s3 ⋆
                exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
                  (BitVec.ofNat 64 out_len') ⋆
                bytes out_ptr buf ⋆ R) m')
            (fun J xs m' ⟨out_len', hlt', hcond', hm'⟩ => by
              c0_hsteps_nogrp
              exact hQ 0#64 c' ext' s3 [] out_len' m' hcmp2 hlen3 hcfg2 hext2
                (Or.inl rfl) hlt' (fun _ => ⟨hcond', hm'⟩) (fun h => absurd rfl h)
                (fun hu _ => absurd hu hnot_ut))
            (fun J hJ => by
              c0_hsteps_nogrp
              dsimp only
              refine wp_load_of hld_len ?_
              c0_hsteps_nogrp
              · dsimp only
                refine wp_store_sep (store_cell64 (a := outDesc + 16#64)
                    (R := FullMem c' s3 ⋆ bytes out_ptr buf ⋆ bytes cnf_ptr cnfBytes ⋆
                      array64 (c'.hdr - 2304) ext' ⋆ cell64 outDesc out_ptr ⋆
                      cell64 (outDesc + 8#64) (BitVec.ofNat 64 buf.length) ⋆ R)
                    0#64 (sep_ac hm3)) fun m4 hm4 => ?_
                c0_hsteps_nogrp
                have hm4_m6 : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s3 ⋆
                    exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length) 0#64 ⋆
                    bytes out_ptr buf ⋆ R) m4 := by
                  have htmp : (FullMem c' s3 ⋆ (array64 (c'.hdr - 2304) ext' ⋆
                      (bytes cnf_ptr cnfBytes ⋆ exportOutMem outDesc out_ptr
                        (BitVec.ofNat 64 buf.length) 0#64 ⋆ bytes out_ptr buf ⋆ R))) m4 := by
                    unfold exportOutMem; exact sep_ac hm4
                  rw [← fullM6HdrMem_iff] at htmp; exact sep_ac htmp
                exact hJ () m4 ⟨0, by decide, Or.inl rfl, hm4_m6⟩
              · have hlt_w : buf.length < written := by
                  have hnc : ¬ written % 2 ^ 64 ≤ buf.length % 2 ^ 64 := ‹_›
                  rw [Nat.mod_eq_of_lt hwr_lt, Nat.mod_eq_of_lt hcap] at hnc
                  exact Nat.lt_of_not_ge hnc
                have hm3_m6 : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s3 ⋆
                    exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
                      (BitVec.ofNat 64 written) ⋆ bytes out_ptr buf ⋆ R) m3 := by
                  have htmp : (FullMem c' s3 ⋆ (array64 (c'.hdr - 2304) ext' ⋆
                      (bytes cnf_ptr cnfBytes ⋆ exportOutMem outDesc out_ptr
                        (BitVec.ofNat 64 buf.length) (BitVec.ofNat 64 written) ⋆
                        bytes out_ptr buf ⋆ R))) m3 := by
                    unfold exportOutMem; exact sep_ac hm3
                  rw [← fullM6HdrMem_iff] at htmp; exact sep_ac htmp
                exact hJ () m3 ⟨written, hwr_lt, Or.inr hlt_w, hm3_m6⟩)
        · have hok_eq1 : ok = 1#64 := hok.elim (fun h0 => absurd h0 ‹ok ≠ 0#64›) id
          obtain ⟨hout_eq, hwr_eq, hwr_le, ⟨cnfOut, hpOut, _, huOut⟩, hm3⟩ := hok1 hok_eq1
          have hm3_m6 : (bytes cnf_ptr cnfBytes ⋆ FullM6HdrMem c' ext' s3 ⋆
              exportOutMem outDesc out_ptr (BitVec.ofNat 64 buf.length)
                (BitVec.ofNat 64 written) ⋆
              bytes out_ptr (outBytes ++ buf.drop written) ⋆ R) m3 := by
            have htmp : (FullMem c' s3 ⋆ (array64 (c'.hdr - 2304) ext' ⋆
                (bytes cnf_ptr cnfBytes ⋆ exportOutMem outDesc out_ptr
                  (BitVec.ofNat 64 buf.length) (BitVec.ofNat 64 written) ⋆
                  bytes out_ptr (outBytes ++ buf.drop written) ⋆ R))) m3 := by
              unfold exportOutMem; exact sep_ac hm3
            rw [← fullM6HdrMem_iff] at htmp; exact sep_ac htmp
          have hwr_pos : 0 < written := by
            rw [hwr_eq, hout_eq]; exact exportStateBytes_len_pos s3.core
          have hu_dim : cnfOut.Unsat → cnfIn.Unsat :=
            fun hu => shiftDownCnf_unsat hcnf_pos (huOut hu)
          have hld_inc : loadVal m3 i64 (c.hdr + 1024#64) = some s3.core.inconsistent := by
            rw [← hcmp2.hdr]
            have hm3_f : (FullMem c' s3 ⋆
                (bytes out_ptr (outBytes ++ buf.drop written) ⋆
                  cell64 (outDesc + 16#64) (BitVec.ofNat 64 written) ⋆ bytes cnf_ptr cnfBytes ⋆
                  array64 (c'.hdr - 2304) ext' ⋆ cell64 outDesc out_ptr ⋆
                  cell64 (outDesc + 8#64) (BitVec.ofNat 64 buf.length) ⋆ R)) m3 := sep_ac hm3
            exact FullArenaTactics.load_full_inconsistent hm3_f
          refine wp_load_of hld_inc ?_
          c0_hsteps_nogrp
          · have hinc_ne : s3.core.inconsistent ≠ 0#64 := ‹_›
            have hout_unsat : outBytes = unsatDimacsBytes := by
              rw [hout_eq]; exact exportStateBytes_inconsistent_eq hinc_ne
            have hunsat0 : cnfIn.Unsat :=
              shiftDownCnf_unsat hcnf_pos (hw3.ext_sound.2 (hw3.inconsistent_sound hinc_ne))
            exact hQ 20#64 c' ext' s3 outBytes written m3 hcmp2 hlen3 hcfg2 hext2
              (Or.inr (Or.inr (Or.inr rfl))) hwr_lt (fun h => absurd h (by decide))
              (fun _ => ⟨hwr_pos, hwr_le, hwr_eq.symm,
                ⟨cnfIn, cnfOut, hparse_in, hpOut, hu_dim⟩,
                fun _ => ⟨hout_unsat, cnfIn, hparse_in, hunsat0⟩,
                fun h => absurd h (by decide), hm3_m6⟩)
              (fun hu _ => absurd hu hnot_ut)
          · exact hQ 1#64 c' ext' s3 outBytes written m3 hcmp2 hlen3 hcfg2 hext2
              (Or.inr (Or.inl rfl)) hwr_lt (fun h => absurd h (by decide))
              (fun _ => ⟨hwr_pos, hwr_le, hwr_eq.symm,
                ⟨cnfIn, cnfOut, hparse_in, hpOut, hu_dim⟩,
                fun h => absurd h (by decide), fun h => absurd h (by decide), hm3_m6⟩)
              (fun hu _ => absurd hu hnot_ut)

end

end LeanQbe.T.Examples.Kissat.ExportCnfEntryProof
