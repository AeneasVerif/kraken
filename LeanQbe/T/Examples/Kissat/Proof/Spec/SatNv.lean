/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
public import LeanQbe.T.Logic.Bytes
public import LeanQbe.T.Logic.MemLemmas
public import Kraken.Mem
public import Kraken.Separation

/-!
# Shared Exact Model-Check & `M6Hdr` Workspace Region Helpers (`Proof.Spec.SatNv`)

Retains only the shared non-SAT components still used across `Dimacs` and `Search`:
1. `kissatCheckModelExactSpec` (used by `Dimacs.Spec` and `Dimacs.Wp2`).
2. `fullM6WorkBase` / `fullM6WorkHdr` alignment & region collapse helpers
   (`region_work_to_m6_workBase`, `region_work_from_m6_hdrMem`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src
open Kraken.Bedrock2.Test

/-- Exact decision specification of `kissat_check_model(cnf_ptr, cnf_end, d, vals, mv_max)`. -/
@[expose] def kissatCheckModelExactSpec : Spec [i64, i64, i64, i64, i64] [i64] :=
  fun (cnf_ptr, cend, d, vals_ptr, mv_max_v, ()) m Q _ =>
    ∃ (mv0 nc0 cur0 val0 : BitVec 64) (cnfBytes valsBytes : List UInt8) (mv_max : Nat)
      (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      mv_max_v = BitVec.ofNat 64 mv_max ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      mv_max < 2 ^ 64 ∧
      2 * mv_max ≤ valsBytes.length ∧
      valsBytes.length ≤ 2 ^ 64 ∧
      (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv0 nc0 cur0 val0 ⋆
        bytes vals_ptr valsBytes ⋆ R) m ∧
      ∀ (r mv' nc' cur' val' : BitVec 64) (m' : Mem 64),
        r = (if runKissatCheckModel cnfBytes valsBytes mv_max then 1#64 else 0#64) →
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d mv' nc' cur' val' ⋆
          bytes vals_ptr valsBytes ⋆ R) m' →
        Q (r, ()) m'

/-- Aligned base address of the `M6Hdr` workspace (`work_ptr + fullAlignPad work_ptr`). -/
@[expose] def fullM6WorkBase (work_ptr : BitVec 64) : BitVec 64 :=
  work_ptr + BitVec.ofNat 64 (fullAlignPad work_ptr)

/-- Aligned `FullHdr *h` pointer placed `fullM6ExtBytes = 2304` bytes past `fullM6WorkBase`. -/
@[expose] def fullM6WorkHdr (work_ptr : BitVec 64) : BitVec 64 :=
  fullM6WorkBase work_ptr + BitVec.ofNat 64 fullM6ExtBytes

theorem m6ExtAddr_fullM6WorkHdr (work_ptr : BitVec 64) :
    m6ExtAddr (fullM6WorkHdr work_ptr) = fullM6WorkBase work_ptr := by
  rw [m6ExtAddr_eq]
  unfold fullM6WorkHdr fullM6ExtBytes
  exact BitVec.add_sub_cancel (fullM6WorkBase work_ptr) (BitVec.ofNat 64 2304)

theorem fullM6WorkBase_toNat_lt {work_ptr : BitVec 64} {wlen : Nat}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hfit : work_ptr.toNat + wlen < 2 ^ 64) :
    (fullM6WorkBase work_ptr).toNat = work_ptr.toNat + fullAlignPad work_ptr := by
  unfold fullM6WorkBase
  exact bv_add_ofNat_toNat (by omega)

theorem fullAlignPad_fullM6WorkBase {work_ptr : BitVec 64} {wlen : Nat}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hfit : work_ptr.toNat + wlen < 2 ^ 64) :
    fullAlignPad (fullM6WorkBase work_ptr) = 0 := by
  have hbt := fullM6WorkBase_toNat_lt hle hfit
  have hmod : (fullM6WorkBase work_ptr).toNat % 8 = 0 := by
    rw [hbt]
    unfold fullAlignPad
    split <;> omega
  unfold fullAlignPad
  simp [hmod]

theorem fullAlignPad_fullM6WorkHdr {work_ptr : BitVec 64} {wlen : Nat}
    (hle : fullAlignPad work_ptr + fullM6HdrTotalBytes ≤ wlen)
    (hfit : work_ptr.toNat + wlen < 2 ^ 64) :
    fullAlignPad (fullM6WorkHdr work_ptr) = 0 := by
  have hbt := fullM6WorkBase_toNat_lt hle hfit
  have hhdr : (fullM6WorkHdr work_ptr).toNat =
      (fullM6WorkBase work_ptr).toNat + fullM6ExtBytes := by
    unfold fullM6WorkHdr fullM6ExtBytes fullM6HdrTotalBytes at *
    exact bv_add_ofNat_toNat (by omega)
  have hmod : (fullM6WorkHdr work_ptr).toNat % 8 = 0 := by
    rw [hhdr, hbt]
    unfold fullM6ExtBytes fullAlignPad
    split <;> omega
  unfold fullAlignPad
  simp [hmod]

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

end LeanQbe.T.Examples.Kissat.Proof.Spec
