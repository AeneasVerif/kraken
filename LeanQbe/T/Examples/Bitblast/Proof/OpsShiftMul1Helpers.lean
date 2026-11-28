/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulHelpers
public import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Factored Invariants & Step Lemmas for Variable Shifts (`Bitblast.Proof.OpsShiftMul1Helpers`)

Separates pure `BitVec` shift-distance bounds, invariant definitions (`ShiftStageInv`,
`ShiftPhase2Inv`, `ShiftInnerInv`, `ShiftOrInv`, `ShiftFillInv`, `ShiftDoneInv`), closing lemmas,
and inner-loop transition proofs from `OpsShiftMul1.lean` so every theorem in `OpsShiftMul1` stays
concise (`<= 420` lines) and every module stays `< 1,350` LOC.
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

/-! ## 1. Pure `BitVec` & `AigInv` Helpers -/

public section

theorem shift1_aig_le_self (g : Aig) : g ≤ g :=
  Aig.extends_rfl g

theorem shift1_aigInv_with_oom {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)}
    {ht : List (BitVec 32)} (haig : AigInv hdr g aw ht) (v : BitVec 32) :
    AigInv { hdr with oom := v } g aw ht :=
  { haig with }

theorem shift1_aigInv_with_lits_len {hdr : BVHdrState} {g : Aig} {aw : List (BitVec 64)}
    {ht : List (BitVec 32)} (haig : AigInv hdr g aw ht) (v : BitVec 32) :
    AigInv { hdr with lits_len := v } g aw ht :=
  { haig with }

theorem shift1_bv32_succ_add {j : Nat} (hj : j + 1 < 2 ^ 32) :
    BitVec.ofNat 32 j + (1 : BitVec 32) = BitVec.ofNat 32 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

theorem shift1_setWidth64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

theorem shift1_nat_shl1_mod {p : Nat} (hp : p < 32) :
    1 * 2 ^ (p % 2 ^ 32 % 64) % 2 ^ 64 = 2 ^ p := by
  have hp32 : p % 2 ^ 32 % 64 = p := by
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [hp32, Nat.one_mul, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))]

theorem shift1_dist_toNat {p : Nat} (hp : p < 32) :
    (BitVec.setWidth 32
      ((1#64 : BitVec 64) <<< ((BitVec.setWidth 64 (BitVec.ofNat 32 p)).toNat % 64))).toNat =
      2 ^ p := by
  have hp64 : (BitVec.setWidth 64 (BitVec.ofNat 32 p)).toNat % 64 = p := by
    rw [shift1_setWidth64_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hlt64 : 2 ^ p < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hlt32 : 2 ^ p < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) hp
  rw [hp64, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft,
    show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt hlt64, Nat.mod_eq_of_lt hlt32]

theorem shift1_sub1_toNat {w : BitVec 32} (hw : 0 < w.toNat) :
    (w - 1#32).toNat = w.toNat - 1 := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
    (by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega))]
  rfl

/-! ## 2. `bv_blast_shift_var` Closing & Step Theorems -/

theorem shiftVar_bad_close {h : BitVec 64} {aOff w bOff nw op : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig} {aw0 : List (BitVec 64)} {ht0 lp0 : List (BitVec 32)}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post [i32]}
    (haig0 : AigInv hdr0 g0 aw0 ht0)
    (hbad : hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
      sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false)
    (hm : (bvHdrMem h { hdr0 with oom := 1#32 } ⋆ array64 hdr0.aig_ptr aw0 ⋆
      array (t := i32) hdr0.ht_ptr ht0 ⋆ array (t := i32) hdr0.lits_ptr lp0 ⋆ R) m0)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (g' : Aig)
      (aigWords' : List (BitVec 64)) (htSlots' litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr0.OpsFrame hdr' → g0 ≤ g' → AigInv hdr' g' aigWords' htSlots' →
      litsPool'.length = lp0.length → hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool'.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr'.oom ≠ 0#32) →
      (hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr'.oom = 0#32 →
        hdr0.oom = 0#32 ∧ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
        ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g' litsPool' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
          SliceDenotes g' ρ (litsSlice litsPool' ret.toNat w.toNat) (bvShiftSem op va vb)) →
      (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aigWords' ⋆
        array (t := i32) hdr'.ht_ptr htSlots' ⋆
        array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Q (0xFFFFFFFF#32, ⟨⟩) m0 :=
  have _ := hbad
  hQ 0xFFFFFFFF#32 { hdr0 with oom := 1#32 } g0 aw0 ht0 lp0 m0
    (ops_lits_pure_guard_oom hdr0).2.2.2 (shift1_aig_le_self g0)
    (shift1_aigInv_with_oom haig0 1#32) rfl (Nat.le_refl _) (fun hc => hc) (fun _ _ => rfl)
    (fun _ => show (1#32 : BitVec 32) ≠ 0#32 from by decide) (fun _ => rfl)
    (fun h0 => absurd h0 (show (1#32 : BitVec 32) ≠ 0#32 from by decide)) hm

theorem shiftVar_oom_close {h : BitVec 64} {aOff w bOff nw op : BitVec 32}
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
      (hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr''.oom ≠ 0#32) →
      (hdr''.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr''.oom = 0#32 →
        hdr0.oom = 0#32 ∧ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
        ret = hdr0.lits_len ∧ hdr''.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g'' litsPool'' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
          SliceDenotes g'' ρ (litsSlice litsPool'' ret.toNat w.toNat) (bvShiftSem op va vb)) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aigWords'' ⋆
        array (t := i32) hdr''.ht_ptr htSlots'' ⋆
        array (t := i32) hdr''.lits_ptr litsPool'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    Q (0xFFFFFFFF#32, ⟨⟩) m' :=
  hQ 0xFFFFFFFF#32 hdr' g' aw' ht' lp' m' hfr hext haig' hlen hl1 (fun _ => hl2) hpre
    (fun _ => hoom) (fun _ => rfl) (fun h0 => absurd h0 hoom) hm

theorem shiftVar_ok_close {h : BitVec 64} {aOff w bOff nw op : BitVec 32}
    {hdr0 hdr' : BVHdrState} {g0 g' : Aig} {aw' : List (BitVec 64)}
    {ht' lp0 lp' : List (BitVec 32)} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i32]}
    (hoom0 : hdr0.oom = 0#32)
    (hop : decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true)
    (hsla : sliceOkBool hdr0 aOff w = true) (hslb : sliceOkBool hdr0 bOff nw = true)
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
    (hsem : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      evalPoolSlice g' ρ lp' hdr0.lits_len.toNat w.toNat = bvShiftSem op va vb)
    (hm : (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
      array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m')
    (hQ : ∀ (ret : BitVec 32) (hdr'' : BVHdrState) (g'' : Aig)
      (aigWords'' : List (BitVec 64)) (htSlots'' litsPool'' : List (BitVec 32)) (m'' : Mem 64),
      hdr0.OpsFrame hdr'' → g0 ≤ g'' → AigInv hdr'' g'' aigWords'' htSlots'' →
      litsPool''.length = lp0.length → hdr0.lits_len.toNat ≤ hdr''.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr''.lits_len.toNat ≤ hdr''.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool''.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr''.oom ≠ 0#32) →
      (hdr''.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr''.oom = 0#32 →
        hdr0.oom = 0#32 ∧ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
        ret = hdr0.lits_len ∧ hdr''.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g'' litsPool'' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
          SliceDenotes g'' ρ (litsSlice litsPool'' ret.toNat w.toNat) (bvShiftSem op va vb)) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aigWords'' ⋆
        array (t := i32) hdr''.ht_ptr htSlots'' ⋆
        array (t := i32) hdr''.lits_ptr litsPool'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    Q (hdr0.lits_len, ⟨⟩) m' := by
  refine hQ hdr0.lits_len hdr' g' aw' ht' lp' m' hfr hext haig' hlen hl1 (fun _ => hl2) hpre
    (fun hbad => by
      rcases hbad with h1 | h1 | h1 | h1
      · exact absurd hoom0 h1
      · rw [hop] at h1; cases h1
      · rw [hsla] at h1; cases h1
      · rw [hslb] at h1; cases h1)
    (fun hne => absurd hoom' hne) (fun _ => ?_) hm
  refine ⟨hoom0, hop, hsla, hslb, rfl, hlen', hwf_out, fun ρ va vb hva hvb => ?_⟩
  rw [← hsem ρ va vb hva hvb]
  exact sliceDenotes_evalPoolSlice (by rw [hlen, hcap0]; exact hfit)

theorem shiftVar_cond_false_step {g0 g : Aig} {lp0 lp : List (BitVec 32)}
    {aOff bOff w op : BitVec 32} {out p nw : Nat}
    (hcond0 : lp.getD (bOff.toNat + p) 0#32 = 0#32)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hb_hi : bOff.toNat + nw ≤ out) (hp : p < nw) (hp2 : 2 ^ p < w.toNat)
    (hop : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (heval : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      evalPoolSlice g ρ lp out w.toNat = bvShiftCur op va vb p)
    (hb_len : bOff.toNat + nw ≤ lp0.length) :
    ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      evalPoolSlice g ρ lp out w.toNat = bvShiftCur op va vb (p + 1) := by
  intro ρ va vb hva hvb
  have hbit : vb.getLsbD p = false := by
    have h1 := hpre (bOff.toNat + p) (by omega)
    rw [hcond0] at h1
    have hv := hvb.2 p hp
    rw [litsSlice_getD hb_len hp, ← h1, evalLit_ofBv_zero] at hv
    exact hv.symm
  rw [heval ρ va vb hva hvb]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [bvShiftCur_step_getLsbD va vb hop hp hp2 hj, hbit]
  rfl

theorem shiftVar_ite_step_ok {g0 g g' : Aig} {lp0 lp lp' : List (BitVec 32)}
    {aOff bOff w op : BitVec 32} {out j p nw : Nat} {sbit ret : BitVec 32}
    (hlen0 : lp.length = lp0.length)
    (hpre_out : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_b : SliceLitsWf g0 lp0 bOff.toNat nw) (hp : p < nw)
    (hwf_out : SliceLitsWf g lp out w.toNat)
    (heval_out : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      evalPoolSlice g ρ lp out w.toNat = bvShiftCur op va vb p)
    (hwf_tmp : ∀ k < j,
      ((lp.getD (out + w.toNat + k) 0#32) >>> 1).toNat < g.A + 1 + g.nodes.size)
    (heval_tmp : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw) (k : Nat),
      k < j → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + w.toNat + k) 0#32)) =
        (bvShiftCur op va vb (p + 1)).getLsbD k)
    (hj : j < w.toNat) (hop : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (hp2 : 2 ^ p < w.toNat) (hwr : out + w.toNat + j < lp.length) (hext : g ≤ g')
    (hret_bd : (ret >>> 1).toNat < g'.A + 1 + g'.nodes.size)
    (hsbit_eval : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g.evalLit ρ (UInt32.ofBitVec sbit) =
        if op = 19#32 then
          if 2 ^ p ≤ j then (bvShiftCur op va vb p).getLsbD (j - 2 ^ p) else false
        else if op = 20#32 then
          if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p) else false
        else
          if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p)
          else (bvShiftCur op va vb p).getLsbD (w.toNat - 1))
    (hret_eval : ∀ ρ : Nat → Bool,
      g'.evalLit ρ (UInt32.ofBitVec ret) =
        cond (g.evalLit ρ (UInt32.ofBitVec (lp0.getD (bOff.toNat + p) 0#32)))
          (g.evalLit ρ (UInt32.ofBitVec sbit))
          (g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + j) 0#32))))
    (hlp' : lp' = lp.set (out + w.toNat + j) ret)
    (hle0 : g0 ≤ g) (hb_len : bOff.toNat + nw ≤ lp0.length) :
    lp'.length = lp0.length ∧
    (∀ q < out, lp'.getD q 0#32 = lp0.getD q 0#32) ∧
    SliceLitsWf g' lp' out w.toNat ∧
    (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      evalPoolSlice g' ρ lp' out w.toNat = bvShiftCur op va vb p) ∧
    (∀ k < j + 1,
      ((lp'.getD (out + w.toNat + k) 0#32) >>> 1).toNat < g'.A + 1 + g'.nodes.size) ∧
    (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw) (k : Nat),
      k < j + 1 → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g'.evalLit ρ (UInt32.ofBitVec (lp'.getD (out + w.toNat + k) 0#32)) =
        (bvShiftCur op va vb (p + 1)).getLsbD k) := by
  subst hlp'
  have hkeep : ∀ q < out + w.toNat,
      (lp.set (out + w.toNat + j) ret).getD q 0#32 = lp.getD q 0#32 := by
    intro q hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
      ← List.getD_eq_getElem?_getD]
  have hsz : g.A + 1 + g.nodes.size ≤ g'.A + 1 + g'.nodes.size := by
    have := hext.1; have := hext.2.1; omega
  refine ⟨by simp [hlen0], fun q hq => (hkeep q (by omega)).trans (hpre_out q hq),
    SliceLitsWf.of_agree (fun k hk => hkeep (out + k) (by omega)) (hwf_out.extend hext),
    fun ρ va vb hva hvb => by
      rw [evalPoolSlice_of_agree (fun k hk => hkeep (out + k) (by omega)),
        evalPoolSlice_extend hext hwf_out]
      exact heval_out ρ va vb hva hvb,
    fun k hk => by
      by_cases hkj : k = j
      · subst hkj; rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some]
        exact hret_bd
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
          ← List.getD_eq_getElem?_getD]
        exact Nat.lt_of_lt_of_le (hwf_tmp k (by omega)) hsz,
    fun ρ va vb k hk hva hvb => by
      by_cases hkj : k = j
      · subst hkj
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some,
          hret_eval ρ]
        have hcond : g.evalLit ρ (UInt32.ofBitVec (lp0.getD (bOff.toNat + p) 0#32)) =
            vb.getLsbD p := by
          rw [Aig.evalLit_extend_node hle0 (by rw [ofBv_shr1_toNat]; exact hwf_b p hp),
            ← litsSlice_getD hb_len hp]
          exact hvb.2 p hp
        have hout_j : g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + k) 0#32)) =
            (bvShiftCur op va vb p).getLsbD k := by
          rw [← evalPoolSlice_getLsbD hj, heval_out ρ va vb hva hvb]
        rw [hcond, hsbit_eval ρ va vb hva hvb, hout_j,
          bvShiftCur_step_getLsbD va vb hop hp hp2 hj]
        cases vb.getLsbD p <;> rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
          ← List.getD_eq_getElem?_getD]
        rw [Aig.evalLit_extend_node hext (by rw [ofBv_shr1_toNat]; exact hwf_tmp k (by omega))]
        exact heval_tmp ρ va vb k (by omega) hva hvb⟩

theorem shiftVar_copy_step_ok {g0 g : Aig} {lp0 lp lp' : List (BitVec 32)}
    {aOff bOff w op : BitVec 32} {out p nw : Nat}
    (hlen' : lp'.length = lp.length) (hlen : lp.length = lp0.length)
    (hout_ag : ∀ q, q < out ∨ out + w.toNat ≤ q → lp'.getD q 0#32 = lp.getD q 0#32)
    (hin_copy : ∀ j < w.toNat,
      lp'.getD (out + j) 0#32 = lp.getD (out + w.toNat + j) 0#32)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_tmp : ∀ k < w.toNat,
      ((lp.getD (out + w.toNat + k) 0#32) >>> 1).toNat < g.A + 1 + g.nodes.size)
    (heval_tmp : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw) (k : Nat),
      k < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + w.toNat + k) 0#32)) =
        (bvShiftCur op va vb (p + 1)).getLsbD k) :
    lp'.length = lp0.length ∧
    (∀ q < out, lp'.getD q 0#32 = lp0.getD q 0#32) ∧
    SliceLitsWf g lp' out w.toNat ∧
    (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      evalPoolSlice g ρ lp' out w.toNat = bvShiftCur op va vb (p + 1)) := by
  refine ⟨hlen'.trans hlen, fun q hq => (hout_ag q (Or.inl hq)).trans (hpre q hq), ?_, ?_⟩
  · intro j hj
    rw [hin_copy j hj]
    exact hwf_tmp j hj
  · intro ρ va vb hva hvb
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    rw [evalPoolSlice_getLsbD hj, hin_copy j hj]
    exact heval_tmp ρ va vb j hj hva hvb

theorem shiftVar_fill_ite_step_ok {g0 g g' : Aig} {lp0 lp lp' : List (BitVec 32)}
    {aOff bOff w op : BitVec 32} {out j p0 nw : Nat}
    {anyHiLit fill ret : BitVec 32}
    (hlen0 : lp.length = lp0.length)
    (hpre : ∀ q < out, lp.getD q 0#32 = lp0.getD q 0#32)
    (hwf_any : (anyHiLit >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hwf_fill : (fill >>> 1).toNat < g.A + 1 + g.nodes.size)
    (hwf_cur : SliceLitsWf g lp out w.toNat)
    (hany_eval : ∀ (ρ : Nat → Bool) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g.evalLit ρ (UInt32.ofBitVec anyHiLit) = anyOrBool (fun i => vb.getLsbD i) p0 nw)
    (hfill_eval : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g.evalLit ρ (UInt32.ofBitVec fill) =
        if op = 21#32 then (bvShiftCur op va vb p0).getLsbD (w.toNat - 1) else false)
    (hbefore : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw) (i : Nat),
      i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + i) 0#32)) =
        if i < j then (bvShiftSem op va vb).getLsbD i
        else (bvShiftCur op va vb p0).getLsbD i)
    (hj : j < w.toNat) (hw : 0 < w.toNat) (hop : op = 19#32 ∨ op = 20#32 ∨ op = 21#32)
    (hpw : w.toNat ≤ 2 ^ p0) (hwr : out + j < lp.length) (hext : g ≤ g')
    (hret_bd : (ret >>> 1).toNat < g'.A + 1 + g'.nodes.size)
    (hret_eval : ∀ ρ : Nat → Bool,
      g'.evalLit ρ (UInt32.ofBitVec ret) =
        cond (g.evalLit ρ (UInt32.ofBitVec anyHiLit))
          (g.evalLit ρ (UInt32.ofBitVec fill))
          (g.evalLit ρ (UInt32.ofBitVec (lp.getD (out + j) 0#32))))
    (hlp' : lp' = lp.set (out + j) ret) (hp0_nw : p0 ≤ nw) :
    lp'.length = lp0.length ∧
    (∀ q < out, lp'.getD q 0#32 = lp0.getD q 0#32) ∧
    (anyHiLit >>> 1).toNat < g'.A + 1 + g'.nodes.size ∧
    (fill >>> 1).toNat < g'.A + 1 + g'.nodes.size ∧
    SliceLitsWf g' lp' out w.toNat ∧
    (∀ (ρ : Nat → Bool) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g'.evalLit ρ (UInt32.ofBitVec anyHiLit) = anyOrBool (fun i => vb.getLsbD i) p0 nw) ∧
    (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g'.evalLit ρ (UInt32.ofBitVec fill) =
        if op = 21#32 then (bvShiftCur op va vb p0).getLsbD (w.toNat - 1) else false) ∧
    (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw) (i : Nat),
      i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      g'.evalLit ρ (UInt32.ofBitVec (lp'.getD (out + i) 0#32)) =
        if i < j + 1 then (bvShiftSem op va vb).getLsbD i
        else (bvShiftCur op va vb p0).getLsbD i) := by
  subst hlp'
  have hsz : g.A + 1 + g.nodes.size ≤ g'.A + 1 + g'.nodes.size := by
    have := hext.1; have := hext.2.1; omega
  refine ⟨by simp [hlen0], fun q hq => ?_, Nat.lt_of_lt_of_le hwf_any hsz,
    Nat.lt_of_lt_of_le hwf_fill hsz, (hwf_cur.extend hext).set_at hwr hret_bd,
    fun ρ vb hvb => ?_, fun ρ va vb hva hvb => ?_, fun ρ va vb i hi hva hvb => ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
      ← List.getD_eq_getElem?_getD]
    exact hpre q hq
  · rw [Aig.evalLit_extend_node hext (by rw [ofBv_shr1_toNat]; exact hwf_any)]
    exact hany_eval ρ vb hvb
  · rw [Aig.evalLit_extend_node hext (by rw [ofBv_shr1_toNat]; exact hwf_fill)]
    exact hfill_eval ρ va vb hva hvb
  · by_cases hij : i = j
    · subst hij
      rw [ite_eq_left (Nat.lt_succ_self i),
        List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some,
        hret_eval ρ, hany_eval ρ vb hvb, hfill_eval ρ va vb hva hvb,
        hbefore ρ va vb i hi hva hvb, ite_eq_right (Nat.lt_irrefl i)]
      cases hhi : anyOrBool (fun x => vb.getLsbD x) p0 nw
      · simp [bvShiftCur_eq_sem_of_no_hi va vb hp0_nw hhi]
      · simp [bvShiftCur_sat_of_hi va vb hop hw hpw hhi hi]
    · rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega),
        ← List.getD_eq_getElem?_getD,
        Aig.evalLit_extend_node hext (by rw [ofBv_shr1_toNat]; exact hwf_cur i hi),
        hbefore ρ va vb i hi hva hvb]
      by_cases hilt : i < j
      · rw [ite_eq_left hilt, ite_eq_left (by omega)]
      · rw [ite_eq_right hilt, ite_eq_right (by omega)]

theorem shiftVar_any_fin_eval {g0 gE : Aig} {lp0 : List (BitVec 32)} {bOff nw : BitVec 32}
    {p0 kE : Nat} {ahE : BitVec 32} (hdone : kE = nw.toNat ∨ ahE = 1#32)
    (hk_hi : kE ≤ nw.toNat)
    (heval_ah : ∀ (ρ : Nat → Bool) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      gE.evalLit ρ (UInt32.ofBitVec ahE) = anyOrBool (fun i => vb.getLsbD i) p0 kE) :
    ∀ (ρ : Nat → Bool) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      gE.evalLit ρ (UInt32.ofBitVec ahE) = anyOrBool (fun i => vb.getLsbD i) p0 nw.toNat := by
  intro ρ vb hvb
  rcases hdone with rfl | rfl
  · exact heval_ah ρ vb hvb
  · rw [evalLit_ofBv_one]; symm
    exact anyOrBool_mono _ hk_hi (by rw [← heval_ah ρ vb hvb, evalLit_ofBv_one])

theorem shiftVar_sbit_in_bounds {gJ : Aig} {lpJ : List (BitVec 32)} {out idx w nw : Nat}
    {va : BitVec w} {vb : BitVec nw} {op : BitVec 32} {p : Nat} {ρ : Nat → Bool}
    (hwf_out : SliceLitsWf gJ lpJ out w)
    (hev_out : evalPoolSlice gJ ρ lpJ out w = bvShiftCur op va vb p)
    (hlp : out + w ≤ lpJ.length) (hi : idx < w) :
    ((lpJ[out + idx]'(by omega) >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) ∧
    gJ.evalLit ρ (UInt32.ofBitVec (lpJ[out + idx]'(by omega))) =
      (bvShiftCur op va vb p).getLsbD idx := by
  have hget : lpJ[out + idx]'(by omega) = lpJ.getD (out + idx) 0#32 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  refine ⟨by rw [hget]; exact hwf_out idx hi, ?_⟩
  rw [hget, ← evalPoolSlice_getLsbD hi, hev_out]

theorem shiftVar_wrap_close {h : BitVec 64} {hdr0 hdr' : BVHdrState} {g0 g' : Aig}
    {aw' : List (BitVec 64)} {ht' lp0 lp' : List (BitVec 32)} {m' : Mem 64}
    {ret aOff w bOff nw op : BitVec 32} {R : Mem 64 → Prop} {Q : Post [i32]}
    {sem : BitVec w.toNat → BitVec nw.toNat → BitVec w.toNat}
    (hop_eq : decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true)
    (hsem : ∀ (va : BitVec w.toNat) (vb : BitVec nw.toNat), bvShiftSem op va vb = sem va vb)
    (hfr : hdr0.OpsFrame hdr') (hext : g0 ≤ g') (haig' : AigInv hdr' g' aw' ht')
    (hlen : lp'.length = lp0.length)
    (hl1 : hdr0.lits_len.toNat ≤ hdr'.lits_len.toNat)
    (hl2 : hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat → hdr'.lits_len.toNat ≤ hdr'.lits_cap.toNat)
    (hpre : ∀ p < hdr0.lits_len.toNat, lp'.getD p 0#32 = lp0.getD p 0#32)
    (hfail : hdr0.oom ≠ 0#32 ∨ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = false ∨
      sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr'.oom ≠ 0#32)
    (hret : hdr'.oom ≠ 0#32 → ret = 0xFFFFFFFF#32)
    (hok : hdr'.oom = 0#32 →
      hdr0.oom = 0#32 ∧ decide (op = 19#32 ∨ op = 20#32 ∨ op = 21#32) = true ∧
      sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
      ret = hdr0.lits_len ∧ hdr'.lits_len = hdr0.lits_len + w ∧
      SliceLitsWf g' lp' ret.toNat w.toNat ∧
      ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
        SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
        SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
        SliceDenotes g' ρ (litsSlice lp' ret.toNat w.toNat) (bvShiftSem op va vb))
    (hm' : (bvHdrMem h hdr' ⋆ array64 hdr'.aig_ptr aw' ⋆
      array (t := i32) hdr'.ht_ptr ht' ⋆ array (t := i32) hdr'.lits_ptr lp' ⋆ R) m')
    (hQ : ∀ (ret : BitVec 32) (hdr'' : BVHdrState) (g'' : Aig)
      (aigWords'' : List (BitVec 64)) (htSlots'' litsPool'' : List (BitVec 32)) (m'' : Mem 64),
      hdr0.OpsFrame hdr'' → g0 ≤ g'' → AigInv hdr'' g'' aigWords'' htSlots'' →
      litsPool''.length = lp0.length → hdr0.lits_len.toNat ≤ hdr''.lits_len.toNat →
      (hdr0.lits_len.toNat ≤ hdr0.lits_cap.toNat →
        hdr''.lits_len.toNat ≤ hdr''.lits_cap.toNat) →
      (∀ p < hdr0.lits_len.toNat, litsPool''.getD p 0#32 = lp0.getD p 0#32) →
      (hdr0.oom ≠ 0#32 ∨ true = false ∨
        sliceOkBool hdr0 aOff w = false ∨ sliceOkBool hdr0 bOff nw = false → hdr''.oom ≠ 0#32) →
      (hdr''.oom ≠ 0#32 → ret = 0xFFFFFFFF#32) →
      (hdr''.oom = 0#32 →
        hdr0.oom = 0#32 ∧ true = true ∧
        sliceOkBool hdr0 aOff w = true ∧ sliceOkBool hdr0 bOff nw = true ∧
        ret = hdr0.lits_len ∧ hdr''.lits_len = hdr0.lits_len + w ∧
        SliceLitsWf g'' litsPool'' ret.toNat w.toNat ∧
        ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
          SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
          SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
          SliceDenotes g'' ρ (litsSlice litsPool'' ret.toNat w.toNat) (sem va vb)) →
      (bvHdrMem h hdr'' ⋆ array64 hdr''.aig_ptr aigWords'' ⋆
        array (t := i32) hdr''.ht_ptr htSlots'' ⋆
        array (t := i32) hdr''.lits_ptr litsPool'' ⋆ R) m'' →
      Q (ret, ⟨⟩) m'') :
    Q (ret, ⟨⟩) m' := by
  have _ := hop_eq
  refine hQ ret hdr' g' aw' ht' lp' m' hfr hext haig' hlen hl1 hl2 hpre
    (fun hbad => hfail (by rcases hbad with h1 | h1 | h1 | h1
                           · exact Or.inl h1
                           · cases h1
                           · exact Or.inr (Or.inr (Or.inl h1))
                           · exact Or.inr (Or.inr (Or.inr h1))))
    hret (fun hoom => ?_) hm'
  obtain ⟨hoom0, _, ha, hb, rret, rlen, rwf, rsem⟩ := hok hoom
  refine ⟨hoom0, rfl, ha, hb, rret, rlen, rwf, fun ρ va vb hva hvb => ?_⟩
  rw [← hsem va vb]
  exact rsem ρ va vb hva hvb

end

/-! ## 3. Shared Loop & Stage Invariant Predicates (`@[expose]`) -/

@[expose] public section

/-- Invariant at exit from the Phase 2 doubling loop / entry to Phase 3 high-bit saturation. -/
def ShiftStageInv (aOff w bOff nw op : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mS : Mem 64) (hptr : BitVec 64) : Prop :=
  let (p, hdrS, gS, awS, htS, lpS) := st
  p ≤ nw.toNat ∧ p < 2 ^ 32 ∧ (p < nw.toNat → w.toNat ≤ 2 ^ p) ∧
  hdr0.OpsFrame hdrS ∧ g0 ≤ gS ∧ AigInv hdrS gS awS htS ∧
  hdrS.oom = 0#32 ∧ hdrS.lits_len = hdr0.lits_len + w ∧
  lpS.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpS.getD q 0#32 = lp0.getD q 0#32) ∧
  SliceLitsWf gS lpS hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    evalPoolSlice gS ρ lpS hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb p) ∧
  (bvHdrMem hptr hdrS ⋆ array64 hdrS.aig_ptr awS ⋆
    array (t := i32) hdrS.ht_ptr htS ⋆ array (t := i32) hdr0.lits_ptr lpS ⋆ R) mS

/-- Invariant across iterations `p` of the Phase 2 power-of-two doubling loop. -/
def ShiftPhase2Inv (aOff w bOff nw op : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mP : Mem 64) (hptr : BitVec 64) : Prop :=
  let (p, hdrP, gP, awP, htP, lpP) := st
  p ≤ nw.toNat ∧ p ≤ 32 ∧
  hdr0.OpsFrame hdrP ∧ g0 ≤ gP ∧ AigInv hdrP gP awP htP ∧
  hdrP.oom = 0#32 ∧ hdrP.lits_len = hdr0.lits_len + w + w ∧
  lpP.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpP.getD q 0#32 = lp0.getD q 0#32) ∧
  SliceLitsWf gP lpP hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    evalPoolSlice gP ρ lpP hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb p) ∧
  (bvHdrMem hptr hdrP ⋆ array64 hdrP.aig_ptr awP ⋆
    array (t := i32) hdrP.ht_ptr htP ⋆ array (t := i32) hdr0.lits_ptr lpP ⋆ R) mP

/-- Invariant across bit index `j` of the inner `tmp[j] = ite(...)` loop in Phase 2. -/
def ShiftInnerInv (aOff w bOff nw op : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop) (p : Nat)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mJ : Mem 64) (hptr : BitVec 64) : Prop :=
  let (j, hdrJ, gJ, awJ, htJ, lpJ) := st
  j ≤ w.toNat ∧ hdr0.OpsFrame hdrJ ∧ g0 ≤ gJ ∧ AigInv hdrJ gJ awJ htJ ∧
  hdrJ.oom = 0#32 ∧ hdrJ.lits_len = hdr0.lits_len + w + w ∧
  lpJ.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpJ.getD q 0#32 = lp0.getD q 0#32) ∧
  SliceLitsWf gJ lpJ hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    evalPoolSlice gJ ρ lpJ hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb p) ∧
  (∀ k < j,
    ((lpJ.getD (hdr0.lits_len.toNat + w.toNat + k) 0#32) >>> 1).toNat <
      gJ.A + 1 + gJ.nodes.size) ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat) (k : Nat),
    k < j → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    gJ.evalLit ρ (UInt32.ofBitVec (lpJ.getD (hdr0.lits_len.toNat + w.toNat + k) 0#32)) =
      (bvShiftCur op va vb (p + 1)).getLsbD k) ∧
  (bvHdrMem hptr hdrJ ⋆ array64 hdrJ.aig_ptr awJ ⋆
    array (t := i32) hdrJ.ht_ptr htJ ⋆ array (t := i32) hdr0.lits_ptr lpJ ⋆ R) mJ

/-- Invariant across index `k` of the Phase 3 `any_hi` OR-reduction loop. -/
def ShiftOrInv (aOff w bOff nw op : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop) (p0 : Nat)
    (st : Nat × BitVec 32 × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32))
    (mK : Mem 64) (hptr : BitVec 64) (lpS : List (BitVec 32)) : Prop :=
  let (k, ah, hdrK, gK, awK, htK) := st
  p0 ≤ k ∧ k ≤ nw.toNat ∧ (ah = 1#32 → p0 < k) ∧
  hdr0.OpsFrame hdrK ∧ g0 ≤ gK ∧ AigInv hdrK gK awK htK ∧
  hdrK.oom = 0#32 ∧ hdrK.lits_len = hdr0.lits_len + w ∧
  ((ah >>> 1).toNat < gK.A + 1 + gK.nodes.size) ∧
  SliceLitsWf gK lpS hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (vb : BitVec nw.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    gK.evalLit ρ (UInt32.ofBitVec ah) = anyOrBool (fun i => vb.getLsbD i) p0 k) ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    evalPoolSlice gK ρ lpS hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb p0) ∧
  (bvHdrMem hptr hdrK ⋆ array64 hdrK.aig_ptr awK ⋆
    array (t := i32) hdrK.ht_ptr htK ⋆ array (t := i32) hdr0.lits_ptr lpS ⋆ R) mK

/-- Invariant across bit index `j` of the final Phase 3 saturation `ite` loop. -/
def ShiftFillInv (aOff w bOff nw op : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop) (p0 : Nat) (anyHiLit fill : BitVec 32)
    (st : Nat × BVHdrState × Aig × List (BitVec 64) × List (BitVec 32) × List (BitVec 32))
    (mL : Mem 64) (hptr : BitVec 64) : Prop :=
  let (j, hdrL, gL, awL, htL, lpL) := st
  j ≤ w.toNat ∧ hdr0.OpsFrame hdrL ∧ g0 ≤ gL ∧ AigInv hdrL gL awL htL ∧
  hdrL.oom = 0#32 ∧ hdrL.lits_len = hdr0.lits_len + w ∧ lpL.length = lp0.length ∧
  (∀ q < hdr0.lits_len.toNat, lpL.getD q 0#32 = lp0.getD q 0#32) ∧
  ((anyHiLit >>> 1).toNat < gL.A + 1 + gL.nodes.size) ∧
  ((fill >>> 1).toNat < gL.A + 1 + gL.nodes.size) ∧
  SliceLitsWf gL lpL hdr0.lits_len.toNat w.toNat ∧
  (∀ (ρ : Nat → Bool) (vb : BitVec nw.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    gL.evalLit ρ (UInt32.ofBitVec anyHiLit) = anyOrBool (fun i => vb.getLsbD i) p0 nw.toNat) ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
    SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    gL.evalLit ρ (UInt32.ofBitVec fill) =
      if op = 21#32 then (bvShiftCur op va vb p0).getLsbD (w.toNat - 1) else false) ∧
  (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat) (i : Nat),
    i < w.toNat → SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
    SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
    gL.evalLit ρ (UInt32.ofBitVec (lpL.getD (hdr0.lits_len.toNat + i) 0#32)) =
      if i < j then (bvShiftSem op va vb).getLsbD i else (bvShiftCur op va vb p0).getLsbD i) ∧
  (bvHdrMem hptr hdrL ⋆ array64 hdrL.aig_ptr awL ⋆
    array (t := i32) hdrL.ht_ptr htL ⋆ array (t := i32) hdr0.lits_ptr lpL ⋆ R) mL

/-- Postcondition at the shared `return out;` join point of `bv_blast_shift_var`. -/
def ShiftDoneInv (aOff w bOff nw op : BitVec 32)
    (hdr0 : BVHdrState) (g0 : Aig) (lp0 : List (BitVec 32))
    (R : Mem 64 → Prop) (hptr : BitVec 64) (mF : Mem 64) : Prop :=
  ∃ (hdrF : BVHdrState) (gF : Aig) (awF : List (BitVec 64)) (htF lpF : List (BitVec 32)),
    hdr0.OpsFrame hdrF ∧ g0 ≤ gF ∧ AigInv hdrF gF awF htF ∧
    hdrF.oom = 0#32 ∧ hdrF.lits_len = hdr0.lits_len + w ∧
    lpF.length = lp0.length ∧
    (∀ q < hdr0.lits_len.toNat, lpF.getD q 0#32 = lp0.getD q 0#32) ∧
    SliceLitsWf gF lpF hdr0.lits_len.toNat w.toNat ∧
    (∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      evalPoolSlice gF ρ lpF hdr0.lits_len.toNat w.toNat = bvShiftSem op va vb) ∧
    (bvHdrMem hptr hdrF ⋆ array64 hdrF.aig_ptr awF ⋆
      array (t := i32) hdrF.ht_ptr htF ⋆ array (t := i32) hdrF.lits_ptr lpF ⋆ R) mF

end

/-! ## 4. Direct Invariant-to-Invariant Transition Lemmas -/

public section

theorem shiftStageInv_tail_done {aOff w bOff nw op : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig} {lp0 : List (BitVec 32)} {R : Mem 64 → Prop}
    {hptr : BitVec 64} {p0 : Nat} {hdrS : BVHdrState} {gS : Aig}
    {awS : List (BitVec 64)} {htS lpS : List (BitVec 32)} {mS : Mem 64}
    (hinv : ShiftStageInv aOff w bOff nw op hdr0 g0 lp0 R (p0, hdrS, gS, awS, htS, lpS) mS hptr)
    (hp0_eq : p0 = nw.toNat) :
    ShiftDoneInv aOff w bOff nw op hdr0 g0 lp0 R hptr mS := by
  rcases hinv with ⟨hp0_nw, _, _, hfrS, hextS, haigS, hoomS, hlenS, hlpS_len, hpreS, hwfS, hevS,
    hmS⟩
  refine ⟨hdrS, gS, awS, htS, lpS, hfrS, hextS, haigS, hoomS, hlenS, hlpS_len, hpreS, hwfS,
    fun ρ va vb hva hvb => ?_, by rw [hfrS.lits_ptr]; exact sep_ac hmS⟩
  rw [hevS ρ va vb hva hvb]
  exact bvShiftCur_eq_sem_of_no_hi va vb hp0_nw
    (by rw [hp0_eq]; exact anyOrBool_le _ (Nat.le_refl _))

theorem shiftOrInv_noHi_done {aOff w bOff nw op : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig} {lp0 : List (BitVec 32)} {R : Mem 64 → Prop}
    {hptr : BitVec 64} {p0 kE : Nat} {hdrE : BVHdrState} {gE : Aig}
    {awE : List (BitVec 64)} {htE lpS : List (BitVec 32)} {mE : Mem 64}
    (hp0_nw : p0 ≤ nw.toNat) (hk_hi : kE ≤ nw.toNat)
    (hdone : kE = nw.toNat ∨ (0#32 : BitVec 32) = 1#32)
    (hlpS_len : lpS.length = lp0.length)
    (hpreS : ∀ q < hdr0.lits_len.toNat, lpS.getD q 0#32 = lp0.getD q 0#32)
    (hinv : ShiftOrInv aOff w bOff nw op hdr0 g0 lp0 R p0
      (kE, 0#32, hdrE, gE, awE, htE) mE hptr lpS) :
    ShiftDoneInv aOff w bOff nw op hdr0 g0 lp0 R hptr mE := by
  rcases hinv with ⟨_, _, _, hfrE, hextE, haigE, hoomE, hlenE, _, hwf_sE, heval_ahE, heval_sE, hmE⟩
  have hany : ∀ (ρ : Nat → Bool) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      gE.evalLit ρ (UInt32.ofBitVec 0#32) = anyOrBool (fun i => vb.getLsbD i) p0 nw.toNat :=
    shiftVar_any_fin_eval hdone hk_hi heval_ahE
  refine ⟨hdrE, gE, awE, htE, lpS, hfrE, hextE, haigE, hoomE, hlenE, hlpS_len, hpreS, hwf_sE,
    fun ρ va vb hva hvb => ?_, by rw [hfrE.lits_ptr]; exact sep_ac hmE⟩
  have hno : anyOrBool (fun i => vb.getLsbD i) p0 nw.toNat = false := by
    rw [← hany ρ vb hvb, evalLit_ofBv_zero]
  rw [heval_sE ρ va vb hva hvb, bvShiftCur_eq_sem_of_no_hi va vb hp0_nw hno]

theorem shiftOrInv_or_step {aOff w bOff nw op : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig} {lp0 : List (BitVec 32)} {R : Mem 64 → Prop}
    {hptr : BitVec 64} {p0 k : Nat} {ah ret : BitVec 32}
    {hdrK hdrN : BVHdrState} {gK gN : Aig}
    {_awK awN : List (BitVec 64)} {_htK htN lpS : List (BitVec 32)} {mN : Mem 64}
    (hk_lo : p0 ≤ k) (hk_lt : k < nw.toNat)
    (hfrK : hdr0.OpsFrame hdrK) (hextK : g0 ≤ gK)
    (hlenK : hdrK.lits_len = hdr0.lits_len + w)
    (hwf_sK : SliceLitsWf gK lpS hdr0.lits_len.toNat w.toNat)
    (heval_ah : ∀ (ρ : Nat → Bool) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      gK.evalLit ρ (UInt32.ofBitVec ah) = anyOrBool (fun i => vb.getLsbD i) p0 k)
    (heval_sK : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw.toNat),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw.toNat) vb →
      evalPoolSlice gK ρ lpS hdr0.lits_len.toNat w.toNat = bvShiftCur op va vb p0)
    (hfrN : hdrK.AigFrame hdrN) (hextN : gK ≤ gN) (haigN : AigInv hdrN gN awN htN)
    (hoomN0 : hdrN.oom = 0#32)
    (hret_bd : (ret >>> 1).toNat < gN.A + 1 + gN.nodes.size)
    (hret_ev : ∀ ρ : Nat → Bool,
      gN.evalLit ρ (UInt32.ofBitVec ret) =
        (gK.evalLit ρ (UInt32.ofBitVec ah) ||
          gK.evalLit ρ (UInt32.ofBitVec (lp0.getD (bOff.toNat + k) 0#32))))
    (hwfb0 : SliceLitsWf g0 lp0 bOff.toNat nw.toNat) (hb_len : bOff.toNat + nw.toNat ≤ lp0.length)
    (hmN : (bvHdrMem hptr hdrN ⋆ array64 hdrN.aig_ptr awN ⋆
      array (t := i32) hdrN.ht_ptr htN ⋆ array (t := i32) hdr0.lits_ptr lpS ⋆ R) mN) :
    ShiftOrInv aOff w bOff nw op hdr0 g0 lp0 R p0
      (k + 1, ret, hdrN, gN, awN, htN) mN hptr lpS := by
  refine ⟨by omega, hk_lt, fun _ => by omega, hfrK.trans hfrN.mono,
    Aig.extends_trans hextK hextN, haigN, hoomN0, hfrN.lits_len.trans hlenK, hret_bd,
    hwf_sK.extend hextN, ?_, ?_, hmN⟩
  · intro ρ vb hvb
    rw [hret_ev ρ, Aig.evalLit_extend_node hextK
        (l := UInt32.ofBitVec (lp0.getD (bOff.toNat + k) 0#32))
        (by rw [ofBv_shr1_toNat]; exact hwfb0 k hk_lt),
      heval_ah ρ vb hvb, ← litsSlice_getD hb_len hk_lt, hvb.2 k hk_lt, anyOrBool_step_hi _ hk_lo]
  · intro ρ va vb hva hvb
    rw [evalPoolSlice_extend hextN hwf_sK]
    exact heval_sK ρ va vb hva hvb

theorem shiftFillInv_done {aOff w bOff nw op : BitVec 32}
    {hdr0 : BVHdrState} {g0 : Aig} {lp0 : List (BitVec 32)} {R : Mem 64 → Prop}
    {hptr : BitVec 64} {p0 : Nat} {ahE fill : BitVec 32}
    {hdrL : BVHdrState} {gL : Aig} {awL : List (BitVec 64)}
    {htL lpL : List (BitVec 32)} {mL : Mem 64}
    (hinv : ShiftFillInv aOff w bOff nw op hdr0 g0 lp0 R p0 ahE fill
      (w.toNat, hdrL, gL, awL, htL, lpL) mL hptr) :
    ShiftDoneInv aOff w bOff nw op hdr0 g0 lp0 R hptr mL := by
  rcases hinv with ⟨_, hfrL, hextL, haigL, hoomL, hlenL, hlpL_len, hpreL, _, _, hwf_sL, _, _,
    hbefL, hmL⟩
  refine ⟨hdrL, gL, awL, htL, lpL, hfrL, hextL, haigL, hoomL, hlenL, hlpL_len, hpreL, hwf_sL,
    fun ρ va vb hva hvb => BitVec.eq_of_getLsbD_eq fun i hi => ?_,
    by rw [hfrL.lits_ptr]; exact sep_ac hmL⟩
  rw [evalPoolSlice_getLsbD hi, hbefL ρ va vb i hi hva hvb, ite_eq_left hi]

theorem shiftInnerInv_to_phase2 {aOff w bOff nw op : BitVec 32}
    {hdr0 hdrJ : BVHdrState} {g0 gJ : Aig} {awJ : List (BitVec 64)}
    {htJ lp0 lpJ lpN : List (BitVec 32)} {R : Mem 64 → Prop} {hptr : BitVec 64} {p : Nat}
    {mJ mN : Mem 64}
    (hp_lt : p < nw.toNat) (hp_lt32 : p < 32)
    (hinv : ShiftInnerInv aOff w bOff nw op hdr0 g0 lp0 R p
      (w.toNat, hdrJ, gJ, awJ, htJ, lpJ) mJ hptr)
    (hlpN_len : lpN.length = lpJ.length)
    (houtN : ∀ q, q < hdr0.lits_len.toNat ∨ hdr0.lits_len.toNat + w.toNat ≤ q →
      lpN.getD q 0#32 = lpJ.getD q 0#32)
    (hinN : ∀ j < w.toNat,
      lpN.getD (hdr0.lits_len.toNat + j) 0#32 =
        lpJ.getD (hdr0.lits_len.toNat + w.toNat + j) 0#32)
    (hmN : (bvHdrMem hptr hdrJ ⋆ array64 hdrJ.aig_ptr awJ ⋆
      array (t := i32) hdrJ.ht_ptr htJ ⋆ array (t := i32) hdrJ.lits_ptr lpN ⋆ R) mN) :
    ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R
      (p + 1, hdrJ, gJ, awJ, htJ, lpN) mN hptr := by
  rcases hinv with ⟨_, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hlpJ_len, hpreJ, _, _, hwf_tmpJ,
    hev_tmpJ, _⟩
  have hcp := shiftVar_copy_step_ok hlpN_len hlpJ_len houtN hinN hpreJ hwf_tmpJ hev_tmpJ
  exact ⟨hp_lt, hp_lt32, hfrJ, hextJ, haigJ, hoomJ, hlenJ, hcp.1, hcp.2.1,
    hcp.2.2.1, hcp.2.2.2, by rw [← hfrJ.lits_ptr]; exact hmN⟩

theorem shiftPhase2Inv_cond_false {aOff w bOff nw op : BitVec 32}
    {hdr0 hdrP : BVHdrState} {g0 gP : Aig} {awP : List (BitVec 64)}
    {htP lp0 lpP : List (BitVec 32)} {R : Mem 64 → Prop} {hptr : BitVec 64} {p : Nat}
    {mP : Mem 64}
    (hp_lt : p < nw.toNat) (hp_lt32 : p < 32) (hp2 : 2 ^ p < w.toNat)
    (hop : op = 19#32 ∨ op = 20#32 ∨ op = 21#32) (hb_len : bOff.toNat + nw.toNat ≤ lp0.length)
    (hb_hi : bOff.toNat + nw.toNat ≤ hdr0.lits_len.toNat)
    (hinv : ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R (p, hdrP, gP, awP, htP, lpP) mP hptr)
    (hcond0 : lpP.getD (bOff.toNat + p) 0#32 = 0#32) :
    ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R
      (p + 1, hdrP, gP, awP, htP, lpP) mP hptr := by
  rcases hinv with ⟨_, _, hfrP, hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP, hevP, hmP⟩
  exact ⟨hp_lt, hp_lt32, hfrP, hextP, haigP, hoomP, hlenP, hlpP_len, hpreP, hwfP,
    shiftVar_cond_false_step hcond0 hpreP hb_hi hp_lt hp2 hop hevP hb_len, hmP⟩

theorem shiftStageInv_of_rel {aOff w bOff nw op : BitVec 32}
    {hdr0 hdrR : BVHdrState} {g0 gR : Aig} {awR : List (BitVec 64)}
    {htR lp0 lpR : List (BitVec 32)} {R : Mem 64 → Prop} {hptr : BitVec 64} {p : Nat}
    {mR mS : Mem 64}
    (hpwR : p < nw.toNat → w.toNat ≤ 2 ^ p)
    (hinv : ShiftPhase2Inv aOff w bOff nw op hdr0 g0 lp0 R
      (p, hdrR, gR, awR, htR, lpR) mR hptr)
    (hmS : (bvHdrMem hptr { hdrR with lits_len := hdr0.lits_len + w } ⋆
      (array64 hdrR.aig_ptr awR ⋆ array (t := i32) hdrR.ht_ptr htR ⋆
        array (t := i32) hdr0.lits_ptr lpR ⋆ R)) mS) :
    ShiftStageInv aOff w bOff nw op hdr0 g0 lp0 R
      (p, { hdrR with lits_len := hdr0.lits_len + w }, gR, awR, htR, lpR) mS hptr := by
  rcases hinv with ⟨hp_nwR, hp_32R, hfrR, hextR, haigR, hoomR, _, hlpR_len, hpreR, hwfR, hevR, _⟩
  have hfrS : hdr0.OpsFrame { hdrR with lits_len := hdr0.lits_len + w } :=
    hfrR.with_lits_len (hdr0.lits_len + w)
  exact ⟨hp_nwR, by omega, hpwR, hfrS, hextR, shift1_aigInv_with_lits_len haigR _,
    hoomR, rfl, hlpR_len, hpreR, hwfR, hevR, sep_ac hmS⟩

theorem shiftVar_sbit_zero_lit {op : BitVec 32} {g0 gJ : Aig} {lp0 : List (BitVec 32)}
    {aOff bOff w : BitVec 32} {nw p j : Nat}
    (hcase : (op = 19#32 ∧ ¬ 2 ^ p ≤ j) ∨ (op ≠ 19#32 ∧ ¬ j < w.toNat - 2 ^ p))
    (hop21 : op = 19#32 ∨ op = 20#32) :
    ((0#32 : BitVec 32) >>> 1).toNat < gJ.A + 1 + gJ.nodes.size ∧
    ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      gJ.evalLit ρ (UInt32.ofBitVec 0#32) =
        if op = 19#32 then
          if 2 ^ p ≤ j then (bvShiftCur op va vb p).getLsbD (j - 2 ^ p) else false
        else if op = 20#32 then
          if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p) else false
        else
          if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p)
          else (bvShiftCur op va vb p).getLsbD (w.toNat - 1) := by
  refine ⟨SliceLitsWf.zero_shr1 gJ, fun ρ _ _ _ _ => ?_⟩
  rw [evalLit_ofBv_zero]
  rcases hcase with ⟨h19, hlt⟩ | ⟨hn19, hge⟩
  · simp [h19, hlt]
  · rcases hop21 with rfl | h20
    · exact absurd rfl hn19
    · simp [h20, hge]

theorem shiftVar_sbit_idx_lit {g0 gJ : Aig} {lp0 lpJ : List (BitVec 32)}
    {aOff bOff w op : BitVec 32} {out idx p j nw : Nat}
    (hwf_out : SliceLitsWf gJ lpJ out w.toNat)
    (hev_out : ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      evalPoolSlice gJ ρ lpJ out w.toNat = bvShiftCur op va vb p)
    (hlp : out + w.toNat ≤ lpJ.length) (hi : idx < w.toNat)
    (hbranch : (op = 19#32 ∧ 2 ^ p ≤ j ∧ idx = j - 2 ^ p) ∨
      (op ≠ 19#32 ∧ op = 20#32 ∧ j < w.toNat - 2 ^ p ∧ idx = j + 2 ^ p) ∨
      (op ≠ 19#32 ∧ op ≠ 20#32 ∧ j < w.toNat - 2 ^ p ∧ idx = j + 2 ^ p) ∨
      (op ≠ 19#32 ∧ op ≠ 20#32 ∧ ¬ j < w.toNat - 2 ^ p ∧ idx = w.toNat - 1)) :
    (((lpJ[out + idx]'(by omega)) >>> 1).toNat < gJ.A + 1 + gJ.nodes.size) ∧
    ∀ (ρ : Nat → Bool) (va : BitVec w.toNat) (vb : BitVec nw),
      SliceDenotes g0 ρ (litsSlice lp0 aOff.toNat w.toNat) va →
      SliceDenotes g0 ρ (litsSlice lp0 bOff.toNat nw) vb →
      gJ.evalLit ρ (UInt32.ofBitVec (lpJ[out + idx]'(by omega))) =
        if op = 19#32 then
          if 2 ^ p ≤ j then (bvShiftCur op va vb p).getLsbD (j - 2 ^ p) else false
        else if op = 20#32 then
          if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p) else false
        else
          if j < w.toNat - 2 ^ p then (bvShiftCur op va vb p).getLsbD (j + 2 ^ p)
          else (bvShiftCur op va vb p).getLsbD (w.toNat - 1) := by
  have hget : lpJ[out + idx]'(by omega) = lpJ.getD (out + idx) 0#32 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  refine ⟨by rw [hget]; exact hwf_out idx hi, fun ρ va vb hva hvb => ?_⟩
  rw [hget, ← evalPoolSlice_getLsbD hi, hev_out ρ va vb hva hvb]
  rcases hbranch with ⟨rfl, hge, rfl⟩ | ⟨hn19, rfl, hlt, rfl⟩ |
      ⟨hn19, hn20, hlt, rfl⟩ | ⟨hn19, hn20, hge, rfl⟩
  · simp [hge]
  · simp [hn19, hlt]
  · simp [hn19, hn20, hlt]
  · simp [hn19, hn20, hge]

theorem shift1_getD_eq_getElem (l : List (BitVec 32)) {i : Nat} (hi : i < l.length) :
    l.getD i 0#32 = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

theorem shift1_wp_join1_fwd {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {Jout : Cont [i32]} {Inv : BitVec 32 → Mem 64 → Prop}
    {entry : Tup Cont [[i32]] → Expr Val Cont rs}
    (hJout : ∀ s m', Inv s m' → Jout (s, ()) m')
    (hentry : ∀ (J : Cont [i32]), (∀ s m', Inv s m' → J (s, ()) m') →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (Expr.group (sig := [[i32]])
      (fun _ => Blocks.cons (fun p => Expr.jump Jout (Arg.var p.fst, ())) Blocks.nil)
      entry) m :=
  wp_join_state (fun s : BitVec 32 => (s, ())) Inv
    (fun _ s m' h => by c0_hsteps; exact hJout s m' h) hentry

end

end LeanQbe.T.Examples.Bitblast.Proof
