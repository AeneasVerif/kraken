/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulHelpers
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Factored Invariants & Step Lemmas for `bv_blast_mul` & `bv_blast_clz`

Separates invariant definitions (`MulInitInv`, `MulZeroInv`, `MulCopyInv`, `MulIteInv`,
`MulOuterInv`, `ClzInitInv`, `ClzOuterInv`, `ClzInnerInv`), closing helpers, and pure `BitVec` /
`Aig` step proofs from stage & top-level WP theorems so every theorem remains `<= 250` lines.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open Std.Tactic.BVDecide
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open Std.ExtHashMap
open LeanQbe.T.Examples.Bitblast.Ref
open LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul

/-! ## 1. Pure `BitVec`, `clzAux`, & `BVHdrState` Helpers -/

public section

theorem mul2_aig_le_self (g : Aig) : g ≤ g :=
  Aig.extends_rfl g

theorem mul2_aigInv_with_oom {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)}
    {ht : List (BitVec 32)} (haig : AigInv hdr g aw ht) (v : BitVec 32) :
    AigInv { hdr with oom := v } g aw ht :=
  { haig with }

theorem mul2_aigInv_with_lits_len {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)}
    {ht : List (BitVec 32)} (haig : AigInv hdr g aw ht) (v : BitVec 32) :
    AigInv { hdr with lits_len := v } g aw ht :=
  { haig with }

theorem mul2_opsFrame_with_lits_len {h0 h1 : BVHdrState} (hfr : h0.OpsFrame h1) (v : BitVec 32) :
    h0.OpsFrame { h1 with lits_len := v } :=
  hfr.with_lits_len v

theorem mul2_bv32_succ_add {j : Nat} (hj : j + 1 < 2 ^ 32) :
    BitVec.ofNat 32 j + (1 : BitVec 32) = BitVec.ofNat 32 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

theorem mul2_setWidth64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem mul2_getD_eq_getElem (l : List (BitVec 32)) {i : Nat} (hi : i < l.length) :
    l.getD i 0#32 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem mul2_sub_eq_toNat {a b : BitVec 32} (hle : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat :=
  BitVec.toNat_sub_of_le (BitVec.le_def.mpr hle)

theorem mul2_sliceOkBool_of_fit {hdr0 hdrS : BVHdrState} {off w : BitVec 32}
    (hfr : hdr0.OpsFrame hdrS)
    (hsla : sliceOkBool hdr0 off w = true)
    (hlen_cap : hdrS.lits_len.toNat ≤ hdrS.lits_cap.toNat)
    (hoff : off.toNat ≤ hdrS.lits_len.toNat)
    (hw_fit : w.toNat ≤ hdrS.lits_len.toNat - off.toNat) :
    sliceOkBool hdrS off w = true := by
  unfold sliceOkBool at hsla ⊢
  simp only [decide_eq_true_eq] at hsla ⊢
  refine ⟨hlen_cap, fun hw => ?_, hoff, hw_fit⟩
  rw [hfr.lits_ptr]
  by_cases ha0 : 0 < w.toNat
  · exact hsla.2.1 ha0
  · exact absurd hw ha0

theorem mul2_clz_bitSelect_shr1_zero (val j : BitVec 32) :
    ((val >>> j &&& 1#32) >>> 1).toNat = 0 := by
  have h1 : (val >>> j &&& 1#32).toNat ≤ 1 := by
    simp [BitVec.toNat_and, Nat.and_one_is_mod]
    omega
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  omega

theorem mul2_clz_bitSelect_wf (g : Aig) (val j : BitVec 32) :
    (((val >>> j &&& 1#32) >>> 1).toNat < g.A + 1 + g.nodes.size) := by
  rw [mul2_clz_bitSelect_shr1_zero]
  omega

theorem clzAux_zero {w : Nat} (va : BitVec w) :
    clzAux va 0 = BitVec.ofNat w w := rfl

theorem clzAux_succ {w k : Nat} (va : BitVec w) :
    clzAux va (k + 1) = if va.getLsbD k = true then BitVec.ofNat w (w - 1 - k) else clzAux va k :=
  rfl

end

/-! ## 2. Closing Helpers for `bv_blast_mul` & `bv_blast_clz` -/

public section

theorem mul_bad_close {h : BitVec 64} {aOff bOff w : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig} {aw0 : List (BitVec 64)} {ht0 lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [i32]}
    (haig0 : AigInv hdr0 g0 aw0 ht0)
    (hbad : hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff w = false)
    (hm : (bvHdrMem h { hdr0 with oom := 1#32 } ⋆ array64 hdr0.aig_ptr aw0 ⋆
      array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R) m0)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ true = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff w = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ true = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff w = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (va * vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Q (0xFFFFFFFF#32, ⟨⟩) m0 :=
  have _ := hbad
  hQ 0xFFFFFFFF#32 { hdr0 with oom := 1#32 } g0 aw0 ht0 lp0 m0
    (ops_lits_pure_guard_oom hdr0).2.2.2 (mul2_aig_le_self g0)
    (mul2_aigInv_with_oom haig0 1#32) rfl (Nat.le_refl _) (fun hc => hc) (fun _ _ => rfl)
    (fun _ => show (1#32 : BitVec 32) ≠ 0#32 from by decide) (fun _ => rfl)
    (fun h0 => absurd h0 (show (1#32 : BitVec 32) ≠ 0#32 from by decide)) hm

theorem mul_oom_close {h : BitVec 64} {aOff bOff w : BitVec 32}
    {hdr0 hdr' : BVHdrState} {g0 g' : Aig} {aw' : List (BitVec 64)}
    {ht' lp0 lp' : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i32]}
    (hfr : hdr0.OpsFrame hdr') (hext : g0 ≤ g') (haig' : AigInv hdr' g' aw' ht')
    (hlen : lp'.length = lp0.length)
    (hl1 : hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hl2 : hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat)
    (hpre : ∀ p < hdr0.lits_len.toNat, lp'.getD p 0#32 = lp0.getD p 0#32)
    (hoom : hdr'.oom ≠ 0#32)
    (hm : (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
      array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m')
    (hQ : ∀ (ret : BitVec 32) (hdr'' : BVHdrState) (g'' : Aig)
      (aigWords'' : List (BitVec 64)) (htSlots'' litsPool'' : List (BitVec 32)) (m'' : Mem 64),
      hdr0.OpsFrame hdr'' → g0 ≤ g'' → AigInv hdr'' g'' aigWords'' htSlots'' →
      litsPool''.length = lp0.length → hdr0.lits_len.toNat ≤ hdr''.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr''.lits_len.toNat ≤ hdr''.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool''.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ true = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff w = false → hdr''.oom ≠ 0#32) →
      (hdr''.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr''.oom = 0#32 →
        hdr0.oom = 0#32 ∧ true = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff w = true ∧
        ret = hdr0.lits_len ∧ hdr''.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g'' litsPool'' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
          SliceDenotes g'' ρ (litsSlice litsPool'' ret.toNat w.toNat) (va * vb)) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aigWords'' ⋆
        array (t := i32) hdr''.ht_ptr htSlots'' ⋆
        array (t := i32) hdr''.lits_ptr litsPool'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    Q (0xFFFFFFFF#32, ⟨⟩) m' :=
  hQ 0xFFFFFFFF#32 hdr' g' aw' ht' lp' m' hfr hext haig' hlen hl1 (fun _ => hl2) hpre
    (fun _ => hoom) (fun _ => rfl) (fun h0 => absurd h0 hoom) hm

theorem mul_ok_close {h : BitVec 64} {aOff bOff w : BitVec 32}
    {hdr0 hdr' : BVHdrState} {g0 g' : Aig} {aw' : List (BitVec 64)}
    {ht' lp0 lp' : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i32]}
    (hoom0 : hdr0.oom = 0#32)
    (hsla : sliceOkBool hdr0 aOff w = true) (hslb : sliceOkBool hdr0 bOff w = true)
    (hfr : hdr0.OpsFrame hdr') (hext : g0 ≤ g') (haig' : AigInv hdr' g' aw' ht')
    (hlen : lp'.length = lp0.length)
    (hl1 : hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hl2 : hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat)
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit : hdr0.lits_len.toNat + w.toNat ≤ hdr0.lits_cap.toNat)
    (hpre : ∀ p < hdr0.lits_len.toNat, lp'.getD p 0#32 = lp0.getD p 0#32)
    (hoom' : hdr'.oom = 0#32)
    (hlen' : hdr'.lits_len = hdr0.lits_len + w)
    (hwf_out : SliceLitsWf g' lp' hdr0.lits_len.toNat w.toNat)
    (hsem : ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice g' ρ lp' hdr0.lits_len.toNat w.toNat = va * vb)
    (hm : (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
      array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m')
    (hQ : ∀ (ret : BitVec 32) (hdr'' : BVHdrState) (g'' : Aig)
      (aigWords'' : List (BitVec 64)) (htSlots'' litsPool'' : List (BitVec 32)) (m'' : Mem 64),
      hdr0.OpsFrame hdr'' → g0 ≤ g'' → AigInv hdr'' g'' aigWords'' htSlots'' →
      litsPool''.length = lp0.length → hdr0.lits_len.toNat ≤ hdr''.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr''.lits_len.toNat ≤ hdr''.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool''.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ true = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff w = false → hdr''.oom ≠ 0#32) →
      (hdr''.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr''.oom = 0#32 →
        hdr0.oom = 0#32 ∧ true = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff w = true ∧
        ret = hdr0.lits_len ∧ hdr''.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g'' litsPool'' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
          SliceDenotes g'' ρ (litsSlice litsPool'' ret.toNat w.toNat) (va * vb)) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aigWords'' ⋆
        array (t := i32) hdr''.ht_ptr htSlots'' ⋆
        array (t := i32) hdr''.lits_ptr litsPool'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    Q (hdr0.lits_len, ⟨⟩) m' := by
  refine hQ hdr0.lits_len hdr' g' aw' ht' lp' m' hfr hext haig' hlen hl1 (fun _ => hl2) hpre
    (fun hbad => by
      rcases hbad with h1 | h1 | h1 | h1
      · exact absurd hoom0 h1
      · cases h1
      · rw [hsla] at h1; cases h1
      · rw [hslb] at h1; cases h1)
    (fun hne => absurd hoom' hne) (fun _ => ?_) hm
  refine ⟨hoom0, rfl, hsla, hslb, rfl, hlen', hwf_out, fun ρ va vb hva hvb => ?_⟩
  rw [← hsem ρ va vb hva hvb]
  exact sliceDenotes_evalPoolSlice (by rw [hlen, hcap0]; exact hfit)

theorem clz_bad_close {h : BitVec 64} {aOff w : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig} {aw0 : List (BitVec 64)} {ht0 lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [i32]}
    (haig0 : AigInv hdr0 g0 aw0 ht0)
    (hbad : hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false)
    (hm : (bvHdrMem h { hdr0 with oom := 1#32 } ⋆ array64 hdr0.aig_ptr aw0 ⋆
      array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R) m0)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ sliceOkBool hdr0 aOff w = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) va.clz) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Q (0xFFFFFFFF#32, ⟨⟩) m0 :=
  have _ := hbad
  hQ 0xFFFFFFFF#32 { hdr0 with oom := 1#32 } g0 aw0 ht0 lp0 m0
    (ops_lits_pure_guard_oom hdr0).2.2.2 (mul2_aig_le_self g0)
    (mul2_aigInv_with_oom haig0 1#32) rfl (Nat.le_refl _) (fun hc => hc) (fun _ _ => rfl)
    (fun _ => show (1#32 : BitVec 32) ≠ 0#32 from by decide) (fun _ => rfl)
    (fun h0 => absurd h0 (show (1#32 : BitVec 32) ≠ 0#32 from by decide)) hm

theorem clz_oom_close {h : BitVec 64} {aOff w : BitVec 32}
    {hdr0 hdr' : BVHdrState} {g0 g' : Aig} {aw' : List (BitVec 64)}
    {ht' lp0 lp' : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i32]}
    (hfr : hdr0.OpsFrame hdr') (hext : g0 ≤ g') (haig' : AigInv hdr' g' aw' ht')
    (hlen : lp'.length = lp0.length)
    (hl1 : hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hl2 : hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat)
    (hpre : ∀ p < hdr0.lits_len.toNat, lp'.getD p 0#32 = lp0.getD p 0#32)
    (hoom : hdr'.oom ≠ 0#32)
    (hm : (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
      array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m')
    (hQ : ∀ (ret : BitVec 32) (hdr'' : BVHdrState) (g'' : Aig)
      (aigWords'' : List (BitVec 64)) (htSlots'' litsPool'' : List (BitVec 32)) (m'' : Mem 64),
      hdr0.OpsFrame hdr'' → g0 ≤ g'' → AigInv hdr'' g'' aigWords'' htSlots'' →
      litsPool''.length = lp0.length → hdr0.lits_len.toNat ≤ hdr''.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr''.lits_len.toNat ≤ hdr''.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool''.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false → hdr''.oom ≠ 0#32) →
      (hdr''.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr''.oom = 0#32 →
        hdr0.oom = 0#32 ∧ sliceOkBool hdr0 aOff w = true ∧
        ret = hdr0.lits_len ∧ hdr''.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g'' litsPool'' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g'' ρ (litsSlice litsPool'' ret.toNat w.toNat) va.clz) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aigWords'' ⋆
        array (t := i32) hdr''.ht_ptr htSlots'' ⋆
        array (t := i32) hdr''.lits_ptr litsPool'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    Q (0xFFFFFFFF#32, ⟨⟩) m' :=
  hQ 0xFFFFFFFF#32 hdr' g' aw' ht' lp' m' hfr hext haig' hlen hl1 (fun _ => hl2) hpre
    (fun _ => hoom) (fun _ => rfl) (fun h0 => absurd h0 hoom) hm

theorem clz_ok_close {h : BitVec 64} {aOff w : BitVec 32}
    {hdr0 hdr' : BVHdrState} {g0 g' : Aig} {aw' : List (BitVec 64)}
    {ht' lp0 lp' : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i32]}
    (hoom0 : hdr0.oom = 0#32) (hsla : sliceOkBool hdr0 aOff w = true)
    (hfr : hdr0.OpsFrame hdr') (hext : g0 ≤ g') (haig' : AigInv hdr' g' aw' ht')
    (hlen : lp'.length = lp0.length)
    (hl1 : hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hl2 : hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat)
    (hcap0 : lp0.length = hdr0.lits_cap.toNat)
    (hfit : hdr0.lits_len.toNat + w.toNat ≤ hdr0.lits_cap.toNat)
    (hpre : ∀ p < hdr0.lits_len.toNat, lp'.getD p 0#32 = lp0.getD p 0#32)
    (hoom' : hdr'.oom = 0#32)
    (hlen' : hdr'.lits_len = hdr0.lits_len + w)
    (hwf_out : SliceLitsWf g' lp' hdr0.lits_len.toNat w.toNat)
    (hsem : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      evalPoolSlice g' ρ lp' hdr0.lits_len.toNat w.toNat = va.clz)
    (hm : (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
      array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m')
    (hQ : ∀ (ret : BitVec 32) (hdr'' : BVHdrState) (g'' : Aig)
      (aigWords'' : List (BitVec 64)) (htSlots'' litsPool'' : List (BitVec 32)) (m'' : Mem 64),
      hdr0.OpsFrame hdr'' → g0 ≤ g'' → AigInv hdr'' g'' aigWords'' htSlots'' →
      litsPool''.length = lp0.length → hdr0.lits_len.toNat ≤ hdr''.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr''.lits_len.toNat ≤ hdr''.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool''.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ sliceOkBool hdr0 aOff w = false → hdr''.oom ≠ 0#32) →
      (hdr''.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr''.oom = 0#32 →
        hdr0.oom = 0#32 ∧ sliceOkBool hdr0 aOff w = true ∧
        ret = hdr0.lits_len ∧ hdr''.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g'' litsPool'' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g'' ρ (litsSlice litsPool'' ret.toNat w.toNat) va.clz) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aigWords'' ⋆
        array (t := i32) hdr''.ht_ptr htSlots'' ⋆
        array (t := i32) hdr''.lits_ptr litsPool'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    Q (hdr0.lits_len, ⟨⟩) m' := by
  refine hQ hdr0.lits_len hdr' g' aw' ht' lp' m' hfr hext haig' hlen hl1 (fun _ => hl2) hpre
    (fun hbad => by
      rcases hbad with h1 | h1
      · exact absurd hoom0 h1
      · rw [hsla] at h1; cases h1)
    (fun hne => absurd hoom' hne) (fun _ => ?_) hm
  refine ⟨hoom0, hsla, rfl, hlen', hwf_out, fun ρ va hva => ?_⟩
  rw [← hsem ρ va hva]
  exact sliceDenotes_evalPoolSlice (by rw [hlen, hcap0]; exact hfit)

end

/-! ## 3. Exposed Invariant Predicates for `bv_blast_mul` & `bv_blast_clz` (`@[expose]`) -/

public section

/-- Invariant across bit index `j` of the initial `out[j] = bv_mk_and(y0, a[j])` loop. -/
@[expose] def MulInitInv (aOff bOff w : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop) (y0 : BitVec 32)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mJ : Mem 64) (hptr : BitVec 64) : Prop :=
  let (j, hdrJ, gJ, awJ, htJ, lpJ) := st
  j ≤ w.toNat ∧ hdr0.OpsFrame hdrJ ∧ g0 ≤ gJ ∧ AigInv hdrJ gJ awJ htJ ∧
  hdrJ.oom = 0#32 ∧ hdrJ.lits_len = hdr0.lits_len + w ∧ lpJ.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpJ.getD q 0#32 = lp0.getD q 0#32) ∧
  ((y0 >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) ∧
  (∀ k < j,
    ((lpJ.getD (hdr0.lits_len.toNat + k) 0#32) >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) ∧
  (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat) (k : Nat),
    k < j → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
    gJ.evalLit ρ (UInt32.ofBitVec (lpJ.getD (hdr0.lits_len.toNat + k) 0#32)) =
      (va.mulRec vb 0).getLsbD k) ∧
  (bvHdrMem hptr hdrJ ⋆ array64 hdrJ.aig_ptr awJ ⋆
    array (t := i32) hdrJ.ht_ptr htJ ⋆ array (t := i32) hdr0.lits_ptr lpJ ⋆ R) mJ

/-- Outer loop invariant (`1 ≤ s ≤ w`) for `bv_blast_mul`. -/
@[expose] def MulOuterInv (aOff bOff w : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mS : Mem 64) (hptr : BitVec 64) : Prop :=
  let (s, hdrS, gS, awS, htS, lpS) := st
  1 ≤ s ∧ s ≤ w.toNat ∧ hdr0.OpsFrame hdrS ∧ g0 ≤ gS ∧ AigInv hdrS gS awS htS ∧
  hdrS.oom = 0#32 ∧ hdrS.lits_len = hdr0.lits_len + w + w ∧ lpS.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpS.getD q 0#32 = lp0.getD q 0#32) ∧
  SliceLitsWf gS lpS hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
    evalPoolSlice gS ρ lpS hdr0.lits_len.toNat w.toNat = va.mulRec vb (s - 1)) ∧
  (bvHdrMem hptr hdrS ⋆ array64 hdrS.aig_ptr awS ⋆
    array (t := i32) hdrS.ht_ptr htS ⋆ array (t := i32) hdr0.lits_ptr lpS ⋆ R) mS

/-- Zero-padding loop invariant (`0 ≤ j ≤ s`) for `shifted[0..<s] = 0u`. -/
@[expose] def MulZeroInv (aOff bOff w : BitVec 32) (s : Nat)
    (hdr0 hdrS : BVHdrState) (g0 gS : Aig) (awS : List (BitVec 64))
    (htS lp0 : List (BitVec 32)) (R : Mem 64 → Prop)
    (st : Nat × List (BitVec 32)) (mZ : Mem 64) (hptr : BitVec 64) : Prop :=
  let (j, lpZ) := st
  j ≤ s ∧ lpZ.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat + w.toNat, lpZ.getD q 0#32 = lp0.getD q 0#32 ∨
    (hdr0.lits_len.toNat ≤ q ∧ q < hdr0.lits_len.toNat + w.toNat)) ∧
  (∀ q < hdr0.lits_len.toNat, lpZ.getD q 0#32 = lp0.getD q 0#32) ∧
  SliceLitsWf gS lpZ hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
    evalPoolSlice gS ρ lpZ hdr0.lits_len.toNat w.toNat = va.mulRec vb (s - 1)) ∧
  (∀ k < j, lpZ.getD (hdr0.lits_len.toNat + w.toNat + k) 0#32 = 0#32) ∧
  (bvHdrMem hptr hdrS ⋆ array64 hdrS.aig_ptr awS ⋆
    array (t := i32) hdrS.ht_ptr htS ⋆ array (t := i32) hdr0.lits_ptr lpZ ⋆ R) mZ

/-- Copy-shifted loop invariant (`s ≤ j ≤ w`) for `shifted[s..<w] = a[0..<w-s]`. -/
@[expose] def MulCopyInv (aOff bOff w : BitVec 32) (s : Nat)
    (hdr0 hdrS : BVHdrState) (g0 gS : Aig) (awS : List (BitVec 64))
    (htS lp0 : List (BitVec 32)) (R : Mem 64 → Prop)
    (st : Nat × List (BitVec 32)) (mC : Mem 64) (hptr : BitVec 64) : Prop :=
  let (j, lpC) := st
  s ≤ j ∧ j ≤ w.toNat ∧ lpC.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpC.getD q 0#32 = lp0.getD q 0#32) ∧
  SliceLitsWf gS lpC hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
    evalPoolSlice gS ρ lpC hdr0.lits_len.toNat w.toNat = va.mulRec vb (s - 1)) ∧
  (∀ k < s, lpC.getD (hdr0.lits_len.toNat + w.toNat + k) 0#32 = 0#32) ∧
  (∀ k, s ≤ k → k < j →
    lpC.getD (hdr0.lits_len.toNat + w.toNat + k) 0#32 = lp0.getD (aOff.toNat + (k - s)) 0#32) ∧
  (bvHdrMem hptr hdrS ⋆ array64 hdrS.aig_ptr awS ⋆
    array (t := i32) hdrS.ht_ptr htS ⋆ array (t := i32) hdr0.lits_ptr lpC ⋆ R) mC

/-- Inner `out[j] = bv_aig_ite(ys, added[j], out[j])` invariant for `bv_blast_mul`. -/
@[expose] def MulIteInv (aOff bOff w : BitVec 32) (s : Nat) (ys added : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mJ : Mem 64) (hptr : BitVec 64) : Prop :=
  let (j, hdrJ, gJ, awJ, htJ, lpJ) := st
  j ≤ w.toNat ∧ hdr0.OpsFrame hdrJ ∧ g0 ≤ gJ ∧ AigInv hdrJ gJ awJ htJ ∧
  hdrJ.oom = 0#32 ∧ hdrJ.lits_len = hdr0.lits_len + w + w + w ∧ lpJ.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpJ.getD q 0#32 = lp0.getD q 0#32) ∧
  ((ys >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) ∧
  SliceLitsWf gJ lpJ added.toNat w.toNat ∧
  SliceLitsWf gJ lpJ hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
    evalPoolSlice gJ ρ lpJ added.toNat w.toNat = va.mulRec vb (s - 1) + (va <<< s)) ∧
  (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat) (i : Nat),
    i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
    gJ.evalLit ρ (UInt32.ofBitVec (lpJ.getD (hdr0.lits_len.toNat + i) 0#32)) =
      if i < j then (va.mulRec vb s).getLsbD i else (va.mulRec vb (s - 1)).getLsbD i) ∧
  (bvHdrMem hptr hdrJ ⋆ array64 hdrJ.aig_ptr awJ ⋆
    array (t := i32) hdrJ.ht_ptr htJ ⋆ array (t := i32) hdr0.lits_ptr lpJ ⋆ R) mJ

/-- Initial `out[j] = (j < 32 ? (w >> j) & 1 : 0)` loop invariant for `bv_blast_clz`. -/
@[expose] def ClzInitInv (w : BitVec 32)
    (hdr0 hdr1 : BVHdrState) (g0 : Aig) (aw0 : List (BitVec 64))
    (ht0 lp0 : List (BitVec 32)) (R : Mem 64 → Prop)
    (st : Nat × List (BitVec 32)) (mJ : Mem 64) (hptr : BitVec 64) : Prop :=
  let (j, lpJ) := st
  j ≤ w.toNat ∧ lpJ.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpJ.getD q 0#32 = lp0.getD q 0#32) ∧
  (∀ k < j, ((lpJ.getD (hdr0.lits_len.toNat + k) 0#32) >>> 1).toNat <
    g0.A + 1 + g0.nodes.size) ∧
  (∀ (ρ : Nat → Bool) (k : Nat), k < j →
    g0.evalLit ρ (UInt32.ofBitVec (lpJ.getD (hdr0.lits_len.toNat + k) 0#32)) =
      (BitVec.ofNat w.toNat w.toNat).getLsbD k) ∧
  (bvHdrMem hptr hdr1 ⋆ array64 hdr1.aig_ptr aw0 ⋆
    array (t := i32) hdr1.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lpJ ⋆ R) mJ

/-- Outer `curr < w` scan invariant for `bv_blast_clz`. -/
@[expose] def ClzOuterInv (aOff w : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mC : Mem 64) (hptr : BitVec 64) : Prop :=
  let (curr, hdrC, gC, awC, htC, lpC) := st
  curr ≤ w.toNat ∧ hdr0.OpsFrame hdrC ∧ g0 ≤ gC ∧ AigInv hdrC gC awC htC ∧
  hdrC.oom = 0#32 ∧ hdrC.lits_len = hdr0.lits_len + w ∧ lpC.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpC.getD q 0#32 = lp0.getD q 0#32) ∧
  SliceLitsWf gC lpC hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    evalPoolSlice gC ρ lpC hdr0.lits_len.toNat w.toNat = clzAux va curr) ∧
  (bvHdrMem hptr hdrC ⋆ array64 hdrC.aig_ptr awC ⋆
    array (t := i32) hdrC.ht_ptr htC ⋆ array (t := i32) hdr0.lits_ptr lpC ⋆ R) mC

/-- Inner `out[j] = bv_aig_ite(xc, cbit, out[j])` loop invariant for `bv_blast_clz`. -/
@[expose] def ClzInnerInv (aOff w : BitVec 32) (curr : Nat) (xc : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mJ : Mem 64) (hptr : BitVec 64) : Prop :=
  let (j, hdrJ, gJ, awJ, htJ, lpJ) := st
  j ≤ w.toNat ∧ hdr0.OpsFrame hdrJ ∧ g0 ≤ gJ ∧ AigInv hdrJ gJ awJ htJ ∧
  hdrJ.oom = 0#32 ∧ hdrJ.lits_len = hdr0.lits_len + w ∧ lpJ.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpJ.getD q 0#32 = lp0.getD q 0#32) ∧
  ((xc >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) ∧
  SliceLitsWf gJ lpJ hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (i : Nat),
    i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    gJ.evalLit ρ (UInt32.ofBitVec (lpJ.getD (hdr0.lits_len.toNat + i) 0#32)) =
      if i < j then (clzAux va (curr + 1)).getLsbD i else (clzAux va curr).getLsbD i) ∧
  (bvHdrMem hptr hdrJ ⋆ array64 hdrJ.aig_ptr awJ ⋆
    array (t := i32) hdrJ.ht_ptr htJ ⋆ array (t := i32) hdr0.lits_ptr lpJ ⋆ R) mJ

end

/-! ## 4. Step & Transition Theorems -/

public section

theorem mul_and_step_ok {g0 g g' : Aig} {lp0 lp lp' : List (BitVec 32)}
    {aOff bOff w : BitVec 32} {out j : Nat} {y0 ret : BitVec 32}
    (hlen0 : lp.length = lp0.length)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_y0 : (y0 >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hwf_a : SliceLitsWf g0 lp0 aOff.toNat w.toNat)
    (hwf_b : SliceLitsWf g0 lp0 bOff.toNat w.toNat)
    (hy0_eq : y0 = lp0.getD bOff.toNat 0#32)
    (hwf_prev : ∀ k < j, ((lp.getD (out + k) 0#32) >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hev_prev : ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat) (k : Nat),
      k < j → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + k) 0#32)) = (va.mulRec vb 0).getLsbD k)
    (hj : j < w.toNat) (hwr : out + j < lp.length) (hext : g ≤ g') (hle0 : g0 ≤ g)
    (ha_len : aOff.toNat + w.toNat ≤ lp0.length) (hb_len : bOff.toNat + w.toNat ≤ lp0.length)
    (hret_bd : (ret >>> 1).toNat < g'.A + 1 + g'.nodes.size)
    (hret_ev : ∀ ρ : Nat → Bool,
      g'.evalLit ρ (UInt32.ofBitVec ret) =
        (g.evalLit ρ (UInt32.ofBitVec y0) &&
          g.evalLit ρ (UInt32.ofBitVec (lp0.getD (aOff.toNat + j) 0#32))))
    (hlp' : lp' = lp.set (out + j) ret) :
    lp'.length = lp0.length ∧
    (∀ q < out, lp'.getD q 0#32 = lp0.getD q 0#32) ∧
    ((y0 >>> 1).toNat < g'.A + 1 + g'.nodes.size) ∧
    (∀ k < j + 1, ((lp'.getD (out + k) 0#32) >>> 1).toNat < g'.A + 1 + g'.nodes.size) ∧
    (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat) (k : Nat),
      k < j + 1 → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      g'.evalLit ρ (UInt32.ofBitVec (lp'.getD (out + k) 0#32)) =
        (va.mulRec vb 0).getLsbD k) := by
  subst hlp'
  have _ := hwf_b
  have hsz : g.A + 1 + g.nodes.size ≤ g'.A + 1 + g'.nodes.size := by
    have := hext.1; have := hext.2.1; omega
  refine ⟨by simp [hlen0], fun q hq => ?_, Nat.lt_of_lt_of_le hwf_y0 hsz, fun k hk => ?_,
    fun ρ va vb k hk hva hvb => ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
    exact hpre q hq
  · by_cases hkj : k = j
    · subst hkj; rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some]
      exact hret_bd
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact Nat.lt_of_lt_of_le (hwf_prev k (by omega)) hsz
  · by_cases hkj : k = j
    · subst hkj
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some, hret_ev ρ,
        hy0_eq]
      have hy : g.evalLit ρ (UInt32.ofBitVec (lp0.getD bOff.toNat 0#32)) = vb.getLsbD 0 := by
        rw [Aig.evalLit_extend_node hle0 (by rw [ofBv_shr1_toNat]; exact hwf_b 0 (by omega)),
          ← Nat.add_zero bOff.toNat, ← litsSlice_getD hb_len (by omega)]
        exact hvb.2 0 (by omega)
      have ha : g.evalLit ρ (UInt32.ofBitVec (lp0.getD (aOff.toNat + k) 0#32)) =
          va.getLsbD k := by
        rw [Aig.evalLit_extend_node hle0 (by rw [ofBv_shr1_toNat]; exact hwf_a k hj),
          ← litsSlice_getD ha_len hj]
        exact hva.2 k hj
      rw [hy, ha, mulRec_zero_getLsbD va vb hj]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      rw [Aig.evalLit_extend_node hext (by rw [ofBv_shr1_toNat]; exact hwf_prev k (by omega))]
      exact hev_prev ρ va vb k (by omega) hva hvb

theorem mulInitInv_to_eval {aOff bOff w : BitVec 32}
    {hdr0 hdrJ : BVHdrState} {g0 gJ : Aig} {awJ : List (BitVec 64)}
    {htJ lp0 lpJ : List (BitVec 32)} {R : Mem 64 → Prop} {hptr y0 : BitVec 64}
    {y0_32 : BitVec 32} {mJ : Mem 64}
    (hinv : MulInitInv aOff bOff w hdr0 g0 lp0 R y0_32
      (w.toNat, hdrJ, gJ, awJ, htJ, lpJ) mJ hptr) :
    SliceLitsWf gJ lpJ hdr0.lits_len.toNat w.toNat ∧
    (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice gJ ρ lpJ hdr0.lits_len.toNat w.toNat = va.mulRec vb 0) := by
  have _ := y0
  rcases hinv with ⟨_, _, _, _, _, _, _, _, _, hwf, hev, _⟩
  refine ⟨hwf, fun ρ va vb hva hvb => BitVec.eq_of_getLsbD_eq fun i hi => ?_⟩
  rw [evalPoolSlice_getLsbD hi, hev ρ va vb i hi hva hvb]

theorem mul_zero_step_ok {g0 gS : Aig} {lp0 lp : List (BitVec 32)}
    {aOff bOff w : BitVec 32} {out s j : Nat}
    (hlen0 : lp.length = lp0.length)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_out : SliceLitsWf gS lp out w.toNat)
    (hev_out : ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice gS ρ lp out w.toNat = va.mulRec vb (s - 1))
    (hzeros : ∀ k < j, lp.getD (out + w.toNat + k) 0#32 = 0#32)
    (hj : j < s) (hs : s ≤ w.toNat) (hwr : out + w.toNat + j < lp.length) :
    (lp.set (out + w.toNat + j) 0#32).length = lp0.length ∧
    (∀ q < out, (lp.set (out + w.toNat + j) 0#32).getD q 0#32 = lp0.getD q 0#32) ∧
    SliceLitsWf gS (lp.set (out + w.toNat + j) 0#32) out w.toNat ∧
    (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice gS ρ (lp.set (out + w.toNat + j) 0#32) out w.toNat = va.mulRec vb (s - 1)) ∧
    (∀ k < j + 1, (lp.set (out + w.toNat + j) 0#32).getD (out + w.toNat + k) 0#32 = 0#32) := by
  have _ := hs
  have hkeep : ∀ q < out + w.toNat,
      (lp.set (out + w.toNat + j) 0#32).getD q 0#32 = lp.getD q 0#32 := by
    intro q hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
  refine ⟨by simp [hlen0], fun q hq => (hkeep q (by omega)).trans (hpre q hq),
    SliceLitsWf.of_agree (fun k hk => hkeep (out + k) (by omega)) hwf_out,
    fun ρ va vb hva hvb => by
      rw [evalPoolSlice_of_agree (fun k hk => hkeep (out + k) (by omega))]
      exact hev_out ρ va vb hva hvb,
    fun k hk => by
      by_cases hkj : k = j
      · subst hkj
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
          ← List.getD_eq_getElem?_getD]
        exact hzeros k (by omega)⟩

theorem mul_copy_step_ok {g0 gS : Aig} {lp0 lp : List (BitVec 32)}
    {aOff bOff w : BitVec 32} {out s j : Nat}
    (hlen0 : lp.length = lp0.length)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_out : SliceLitsWf gS lp out w.toNat)
    (hev_out : ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice gS ρ lp out w.toNat = va.mulRec vb (s - 1))
    (hzeros : ∀ k < s, lp.getD (out + w.toNat + k) 0#32 = 0#32)
    (hcopies : ∀ k, s ≤ k → k < j →
      lp.getD (out + w.toNat + k) 0#32 = lp0.getD (aOff.toNat + (k - s)) 0#32)
    (ha_hi : aOff.toNat + w.toNat ≤ out)
    (hs : s ≤ j) (hj : j < w.toNat) (hwr : out + w.toNat + j < lp.length) :
    let v := lp.getD (aOff.toNat + (j - s)) 0#32
    (lp.set (out + w.toNat + j) v).length = lp0.length ∧
    (∀ q < out, (lp.set (out + w.toNat + j) v).getD q 0#32 = lp0.getD q 0#32) ∧
    SliceLitsWf gS (lp.set (out + w.toNat + j) v) out w.toNat ∧
    (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice gS ρ (lp.set (out + w.toNat + j) v) out w.toNat = va.mulRec vb (s - 1)) ∧
    (∀ k < s, (lp.set (out + w.toNat + j) v).getD (out + w.toNat + k) 0#32 = 0#32) ∧
    (∀ k, s ≤ k → k < j + 1 →
      (lp.set (out + w.toNat + j) v).getD (out + w.toNat + k) 0#32 =
        lp0.getD (aOff.toNat + (k - s)) 0#32) := by
  intro v
  have hv_eq : v = lp0.getD (aOff.toNat + (j - s)) 0#32 := hpre _ (by omega)
  have hkeep : ∀ q < out + w.toNat,
      (lp.set (out + w.toNat + j) v).getD q 0#32 = lp.getD q 0#32 := by
    intro q hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
  refine ⟨by simp [hlen0], fun q hq => (hkeep q (by omega)).trans (hpre q hq),
    SliceLitsWf.of_agree (fun k hk => hkeep (out + k) (by omega)) hwf_out,
    fun ρ va vb hva hvb => by
      rw [evalPoolSlice_of_agree (fun k hk => hkeep (out + k) (by omega))]
      exact hev_out ρ va vb hva hvb,
    fun k hk => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hzeros k hk,
    fun k hsk hkj => by
      by_cases hk : k = j
      · subst hk; rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some,
          hv_eq]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
          ← List.getD_eq_getElem?_getD]
        exact hcopies k hsk (by omega)⟩

theorem mul_shifted_wf_eval {g0 gS : Aig} {lp0 lp : List (BitVec 32)}
    {aOff w : BitVec 32} {out s : Nat}
    (hs_lt : s < w.toNat) (hle : g0 ≤ gS)
    (hwf_a : SliceLitsWf g0 lp0 aOff.toNat w.toNat)
    (_hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (_ha_hi : aOff.toNat + w.toNat ≤ out) (ha_len : aOff.toNat + w.toNat ≤ lp0.length)
    (hzeros : ∀ k < s, lp.getD (out + w.toNat + k) 0#32 = 0#32)
    (hcopies : ∀ k, s ≤ k → k < w.toNat →
      lp.getD (out + w.toNat + k) 0#32 = lp0.getD (aOff.toNat + (k - s)) 0#32) :
    SliceLitsWf gS lp (out + w.toNat) w.toNat ∧
    ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      evalPoolSlice gS ρ lp (out + w.toNat) w.toNat = va <<< s := by
  refine ⟨fun k hk => ?_, fun ρ va hva => ?_⟩
  · by_cases hks : k < s
    · rw [hzeros k hks]; exact SliceLitsWf.zero_shr1 gS
    · rw [hcopies k (by omega) hk]
      have hsz : g0.A + 1 + g0.nodes.size ≤ gS.A + 1 + gS.nodes.size := by
        have := hle.1; have := hle.2.1; omega
      exact Nat.lt_of_lt_of_le (hwf_a (k - s) (by omega)) hsz
  · rw [evalPoolSlice_shifted (pool0 := lp0) (aOff := aOff.toNat) hs_lt hzeros hcopies]
    have ha_eq : evalPoolSlice gS ρ lp0 aOff.toNat w.toNat = va := by
      have ha_ev : evalPoolSlice g0 ρ lp0 aOff.toNat w.toNat = va := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [evalPoolSlice_getLsbD hi, ← litsSlice_getD ha_len hi]
        exact hva.2 i hi
      rw [evalPoolSlice_extend hle hwf_a, ha_ev]
    rw [ha_eq]

theorem mul_ite_step_ok {g0 g g' : Aig} {lp0 lp lp' : List (BitVec 32)}
    {aOff bOff w : BitVec 32} {out s j : Nat} {ys added ret : BitVec 32}
    (hlen0 : lp.length = lp0.length)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_ys : (ys >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hy_eq : ys = lp0.getD (bOff.toNat + s) 0#32)
    (hwf_b : SliceLitsWf g0 lp0 bOff.toNat w.toNat)
    (hwf_added : SliceLitsWf g lp added.toNat w.toNat)
    (hwf_out : SliceLitsWf g lp out w.toNat)
    (hev_added : ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice g ρ lp added.toNat w.toNat = va.mulRec vb (s - 1) + (va <<< s))
    (hbefore : ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat) (i : Nat),
      i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + i) 0#32)) =
        if i < j then (va.mulRec vb s).getLsbD i else (va.mulRec vb (s - 1)).getLsbD i)
    (hs1 : 1 ≤ s) (hs_lt : s < w.toNat) (hj : j < w.toNat)
    (hadded_lo : out + w.toNat ≤ added.toNat)
    (hwr : out + j < lp.length) (hb_len : bOff.toNat + w.toNat ≤ lp0.length)
    (hle0 : g0 ≤ g) (hext : g ≤ g')
    (hret_bd : (ret >>> 1).toNat < g'.A + 1 + g'.nodes.size)
    (hret_ev : ∀ ρ : Nat → Bool,
      g'.evalLit ρ (UInt32.ofBitVec ret) =
        cond (g.evalLit ρ (UInt32.ofBitVec ys))
          (g.evalLit ρ (UInt32.ofBitVec (lp.getD (added.toNat + j) 0#32)))
          (g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + j) 0#32))))
    (hlp' : lp' = lp.set (out + j) ret) :
    lp'.length = lp0.length ∧
    (∀ q < out, lp'.getD q 0#32 = lp0.getD q 0#32) ∧
    ((ys >>> 1).toNat < g'.A + 1 + g'.nodes.size) ∧
    SliceLitsWf g' lp' added.toNat w.toNat ∧
    SliceLitsWf g' lp' out w.toNat ∧
    (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice g' ρ lp' added.toNat w.toNat = va.mulRec vb (s - 1) + (va <<< s)) ∧
    (∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat) (i : Nat),
      i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      g'.evalLit ρ (UInt32.ofBitVec (lp'.getD (out + i) 0#32)) =
        if i < j + 1 then (va.mulRec vb s).getLsbD i else (va.mulRec vb (s - 1)).getLsbD i) := by
  subst hlp'
  have hsz : g.A + 1 + g.nodes.size ≤ g'.A + 1 + g'.nodes.size := by
    have := hext.1; have := hext.2.1; omega
  have hkeep_hi : ∀ q, added.toNat ≤ q →
      (lp.set (out + j) ret).getD q 0#32 = lp.getD q 0#32 := by
    intro q hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
  refine ⟨by simp [hlen0],
    fun q hq => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hpre q hq,
    Nat.lt_of_lt_of_le hwf_ys hsz,
    SliceLitsWf.of_agree (fun k hk => hkeep_hi (added.toNat + k) (by omega))
      (hwf_added.extend hext),
    (hwf_out.extend hext).set_at hwr hret_bd,
    fun ρ va vb hva hvb => by
      rw [evalPoolSlice_of_agree (fun k hk => hkeep_hi (added.toNat + k) (by omega)),
        evalPoolSlice_extend hext hwf_added]
      exact hev_added ρ va vb hva hvb,
    fun ρ va vb i hi hva hvb => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left (Nat.lt_succ_self i),
      List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some,
      hret_ev ρ, hy_eq]
    have hys_ev : g.evalLit ρ (UInt32.ofBitVec (lp0.getD (bOff.toNat + s) 0#32)) =
        vb.getLsbD s := by
      rw [Aig.evalLit_extend_node hle0 (by rw [ofBv_shr1_toNat]; exact hwf_b s hs_lt),
        ← litsSlice_getD hb_len hs_lt]
      exact hvb.2 s hs_lt
    have hadd_i : g.evalLit ρ (UInt32.ofBitVec (lp.getD (added.toNat + i) 0#32)) =
        (va.mulRec vb (s - 1) + (va <<< s)).getLsbD i := by
      rw [← evalPoolSlice_getLsbD hj, hev_added ρ va vb hva hvb]
    have hout_i : g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + i) 0#32)) =
        (va.mulRec vb (s - 1)).getLsbD i := by
      rw [hbefore ρ va vb i hi hva hvb, ite_eq_right (Nat.lt_irrefl i)]
    have hrec : va.mulRec vb s = va.mulRec vb (s - 1) +
        if vb.getLsbD s = true then va <<< s else 0 := by
      have h1 := BitVec.mulRec_succ_eq va vb (s - 1)
      rwa [show s - 1 + 1 = s from by omega] at h1
    rw [hys_ev, hadd_i, hout_i, hrec]
    cases hb : vb.getLsbD s <;> simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD,
      Aig.evalLit_extend_node hext (by rw [ofBv_shr1_toNat]; exact hwf_out i hi),
      hbefore ρ va vb i hi hva hvb]
    by_cases hilt : i < j
    · rw [ite_eq_left hilt, ite_eq_left (by omega)]
    · rw [ite_eq_right hilt, ite_eq_right (by omega)]

theorem mul_skip_step_ok {g0 gS : Aig} {lp0 lpS : List (BitVec 32)}
    {aOff bOff w : BitVec 32} {out s : Nat}
    (hys0 : lpS.getD (bOff.toNat + s) 0#32 = 0#32)
    (hpre : ∀ q < out, lpS.getD q 0#32 = lp0.getD q 0#32)
    (hb_hi : bOff.toNat + w.toNat ≤ out) (hb_len : bOff.toNat + w.toNat ≤ lp0.length)
    (hs1 : 1 ≤ s) (hs_lt : s < w.toNat)
    (hev : ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice gS ρ lpS out w.toNat = va.mulRec vb (s - 1)) :
    ∀ (ρ : Nat → Bool) (va vb : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat w.toNat) vb →
      evalPoolSlice gS ρ lpS out w.toNat = va.mulRec vb s := by
  intro ρ va vb hva hvb
  have hbit : vb.getLsbD s = false := by
    have h1 := hpre (bOff.toNat + s) (by omega)
    rw [hys0] at h1
    have hv := hvb.2 s hs_lt
    rw [litsSlice_getD hb_len hs_lt, ← h1, evalLit_ofBv_zero] at hv
    exact hv.symm
  have hrec : va.mulRec vb s = va.mulRec vb (s - 1) := by
    have h1 := BitVec.mulRec_succ_eq va vb (s - 1)
    rw [show s - 1 + 1 = s from by omega, hbit] at h1
    simpa using h1
  rw [hrec]
  exact hev ρ va vb hva hvb

theorem mulIteInv_done {aOff bOff w : BitVec 32} {s : Nat} {ys added : BitVec 32}
    {hdr0 hdrJ : BVHdrState} {g0 gJ : Aig} {awJ : List (BitVec 64)}
    {htJ lp0 lpJ : List (BitVec 32)} {R : Mem 64 → Prop} {hptr : BitVec 64} {mJ : Mem 64}
    (hs1 : 1 ≤ s) (hs_lt : s < w.toNat) (hmJ_ptr : hdrJ.lits_ptr = hdr0.lits_ptr)
    (hinv : MulIteInv aOff bOff w s ys added hdr0 g0 lp0 R
      (w.toNat, hdrJ, gJ, awJ, htJ, lpJ) mJ hptr) :
    let hdrR := { hdrJ with lits_len := hdr0.lits_len + w + w }
    ∀ mR, (bvHdrMem hptr hdrR ⋆ array64 hdrR.aig_ptr awJ ⋆
      array (t := i32) hdrR.ht_ptr htJ ⋆ array (t := i32) hdr0.lits_ptr lpJ ⋆ R) mR →
    MulOuterInv aOff bOff w hdr0 g0 lp0 R (s + 1, hdrR, gJ, awJ, htJ, lpJ) mR hptr := by
  intro hdrR mR hmR
  have _ := hmJ_ptr
  rcases hinv with ⟨_, hfrJ, hextJ, haigJ, hoomJ, _, hlpJ_len, hpreJ, _, _, hwf_outJ, _, hbefJ, _⟩
  refine ⟨by omega, by omega, mul2_opsFrame_with_lits_len hfrJ _, hextJ,
    mul2_aigInv_with_lits_len haigJ _, hoomJ, rfl, hlpJ_len, hpreJ, hwf_outJ,
    fun ρ va vb hva hvb => BitVec.eq_of_getLsbD_eq fun i hi => ?_, hmR⟩
  rw [evalPoolSlice_getLsbD hi, hbefJ ρ va vb i hi hva hvb, ite_eq_left hi,
    Nat.add_sub_cancel]

theorem clz_init_step_ok {g0 : Aig} {lp0 lp : List (BitVec 32)}
    {out j : Nat} {w v : BitVec 32}
    (hlen0 : lp.length = lp0.length)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_prev : ∀ k < j, ((lp.getD (out + k) 0#32) >>> 1).toNat < g0.A + 1 + g0.nodes.size)
    (hev_prev : ∀ (ρ : Nat → Bool) (k : Nat),
      k < j → g0.evalLit ρ (UInt32.ofBitVec (lp.getD (out + k) 0#32)) =
        (BitVec.ofNat w.toNat w.toNat).getLsbD k)
    (hj : j < w.toNat) (hj32 : (BitVec.ofNat 32 j).toNat = j)
    (hwr : out + j < lp.length)
    (hv_eq : v = if BitVec.ofNat 32 j < 32#32 then w >>> BitVec.ofNat 32 j &&& 1#32 else 0#32) :
    (lp.set (out + j) v).length = lp0.length ∧
    (∀ q < out, (lp.set (out + j) v).getD q 0#32 = lp0.getD q 0#32) ∧
    (∀ k < j + 1,
      (((lp.set (out + j) v).getD (out + k) 0#32) >>> 1).toNat < g0.A + 1 + g0.nodes.size) ∧
    (∀ (ρ : Nat → Bool) (k : Nat), k < j + 1 →
      g0.evalLit ρ (UInt32.ofBitVec ((lp.set (out + j) v).getD (out + k) 0#32)) =
        (BitVec.ofNat w.toNat w.toNat).getLsbD k) := by
  subst hv_eq
  refine ⟨by simp [hlen0],
    fun q hq => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hpre q hq,
    fun k hk => ?_, fun ρ k hk => ?_⟩
  · by_cases hkj : k = j
    · subst hkj; rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some]
      split
      · exact mul2_clz_bitSelect_wf g0 w (BitVec.ofNat 32 k)
      · exact SliceLitsWf.zero_shr1 g0
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hwf_prev k (by omega)
  · by_cases hkj : k = j
    · subst hkj; rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some]
      have hb := evalLit_bitSelect (g := g0) (ρ := ρ) (v := w) (w := w) (j := BitVec.ofNat 32 k)
        (by rw [hj32]; exact hj)
      rw [hj32] at hb
      exact hb
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hev_prev ρ k (by omega)

theorem clz_skip_step_ok {g0 gC : Aig} {lp0 lpC : List (BitVec 32)}
    {aOff w : BitVec 32} {out curr : Nat}
    (hxc0 : lpC.getD (aOff.toNat + curr) 0#32 = 0#32)
    (hpre : ∀ q < out, lpC.getD q 0#32 = lp0.getD q 0#32)
    (ha_hi : aOff.toNat + w.toNat ≤ out) (ha_len : aOff.toNat + w.toNat ≤ lp0.length)
    (hcurr : curr < w.toNat)
    (hev : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      evalPoolSlice gC ρ lpC out w.toNat = clzAux va curr) :
    ∀ (ρ : Nat → Bool) (va : BitVec w.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      evalPoolSlice gC ρ lpC out w.toNat = clzAux va (curr + 1) := by
  intro ρ va hva
  have hbit : va.getLsbD curr = false := by
    have h1 := hpre (aOff.toNat + curr) (by omega)
    rw [hxc0] at h1
    have hv := hva.2 curr hcurr
    rw [litsSlice_getD ha_len hcurr, ← h1, evalLit_ofBv_zero] at hv
    exact hv.symm
  rw [clzAux_succ, hbit]
  exact hev ρ va hva

theorem clz_ite_step_ok {g0 g g' : Aig} {lp0 lp lp' : List (BitVec 32)}
    {aOff w val ret : BitVec 32} {out curr j : Nat} {xc : BitVec 32}
    (hlen0 : lp.length = lp0.length)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_xc : (xc >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hxc_eq : xc = lp0.getD (aOff.toNat + curr) 0#32)
    (hwf_a : SliceLitsWf g0 lp0 aOff.toNat w.toNat)
    (hwf_out : SliceLitsWf g lp out w.toNat)
    (hbefore : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (i : Nat),
      i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + i) 0#32)) =
        if i < j then (clzAux va (curr + 1)).getLsbD i else (clzAux va curr).getLsbD i)
    (hval_eq : val.toNat = w.toNat - 1 - curr)
    (hcurr : curr < w.toNat) (hj : j < w.toNat) (hj32 : (BitVec.ofNat 32 j).toNat = j)
    (hwr : out + j < lp.length) (ha_len : aOff.toNat + w.toNat ≤ lp0.length)
    (hle0 : g0 ≤ g) (hext : g ≤ g')
    (hret_bd : (ret >>> 1).toNat < g'.A + 1 + g'.nodes.size)
    (hret_ev : ∀ ρ : Nat → Bool,
      g'.evalLit ρ (UInt32.ofBitVec ret) =
        cond (g.evalLit ρ (UInt32.ofBitVec xc))
          (g.evalLit ρ (UInt32.ofBitVec
            (if BitVec.ofNat 32 j < 32#32 then val >>> BitVec.ofNat 32 j &&& 1#32 else 0#32)))
          (g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + j) 0#32))))
    (hlp' : lp' = lp.set (out + j) ret) :
    lp'.length = lp0.length ∧
    (∀ q < out, lp'.getD q 0#32 = lp0.getD q 0#32) ∧
    ((xc >>> 1).toNat < g'.A + 1 + g'.nodes.size) ∧
    SliceLitsWf g' lp' out w.toNat ∧
    (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (i : Nat),
      i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      g'.evalLit ρ (UInt32.ofBitVec (lp'.getD (out + i) 0#32)) =
        if i < j + 1 then (clzAux va (curr + 1)).getLsbD i else (clzAux va curr).getLsbD i) := by
  subst hlp'
  have hsz : g.A + 1 + g.nodes.size ≤ g'.A + 1 + g'.nodes.size := by
    have := hext.1; have := hext.2.1; omega
  refine ⟨by simp [hlen0],
    fun q hq => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD]
      exact hpre q hq,
    Nat.lt_of_lt_of_le hwf_xc hsz,
    (hwf_out.extend hext).set_at hwr hret_bd,
    fun ρ va i hi hva => ?_⟩
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left (Nat.lt_succ_self i),
      List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some,
      hret_ev ρ, hxc_eq]
    have hxc_ev : g.evalLit ρ (UInt32.ofBitVec (lp0.getD (aOff.toNat + curr) 0#32)) =
        va.getLsbD curr := by
      rw [Aig.evalLit_extend_node hle0 (by rw [ofBv_shr1_toNat]; exact hwf_a curr hcurr),
        ← litsSlice_getD ha_len hcurr]
      exact hva.2 curr hcurr
    have hcbit_ev : g.evalLit ρ (UInt32.ofBitVec
          (if BitVec.ofNat 32 i < 32#32 then val >>> BitVec.ofNat 32 i &&& 1#32 else 0#32)) =
        (BitVec.ofNat w.toNat (w.toNat - 1 - curr)).getLsbD i := by
      have hb := evalLit_bitSelect (g := g) (ρ := ρ) (v := val) (w := w) (j := BitVec.ofNat 32 i)
        (by rw [hj32]; exact hi)
      rw [hj32, hval_eq] at hb
      exact hb
    have hout_ev : g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + i) 0#32)) =
        (clzAux va curr).getLsbD i := by
      rw [hbefore ρ va i hi hva, ite_eq_right (Nat.lt_irrefl i)]
    rw [hxc_ev, hcbit_ev, hout_ev, clzAux_succ]
    cases hb : va.getLsbD curr <;> simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), ← List.getD_eq_getElem?_getD,
      Aig.evalLit_extend_node hext (by rw [ofBv_shr1_toNat]; exact hwf_out i hi),
      hbefore ρ va i hi hva]
    by_cases hilt : i < j
    · rw [ite_eq_left hilt, ite_eq_left (by omega)]
    · rw [ite_eq_right hilt, ite_eq_right (by omega)]

theorem clzInnerInv_done {aOff w : BitVec 32} {curr : Nat} {xc : BitVec 32}
    {hdr0 hdrJ : BVHdrState} {g0 gJ : Aig} {awJ : List (BitVec 64)}
    {htJ lp0 lpJ : List (BitVec 32)} {R : Mem 64 → Prop} {hptr : BitVec 64} {mJ : Mem 64}
    (hcurr : curr < w.toNat)
    (hinv : ClzInnerInv aOff w curr xc hdr0 g0 lp0 R
      (w.toNat, hdrJ, gJ, awJ, htJ, lpJ) mJ hptr) :
    ClzOuterInv aOff w hdr0 g0 lp0 R (curr + 1, hdrJ, gJ, awJ, htJ, lpJ) mJ hptr := by
  rcases hinv with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, _, hwf_outJ, hbefJ, hmJ⟩
  refine ⟨by omega, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, hwf_outJ,
    fun ρ va hva => BitVec.eq_of_getLsbD_eq fun i hi => ?_, hmJ⟩
  rw [evalPoolSlice_getLsbD hi, hbefJ ρ va i hi hva, ite_eq_left hi]

end

end LeanQbe.T.Examples.Bitblast.Proof
