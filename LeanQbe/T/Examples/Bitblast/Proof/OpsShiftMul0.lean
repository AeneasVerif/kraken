/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulSpecs
import LeanQbe.T.Examples.Bitblast.Proof.OpsShiftMulHelpers
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.ProofKit
import LeanQbe.T.Logic.MemLemmas

/-!
# Copy & Pure-Lits Shift/Rotate/Reverse WP Proofs (`Bitblast.Proof.OpsShiftMul0`)

Proves `Γ`-parametric canonical `Func.wp` theorems (`<= 420` lines each) for the `6` pure `lits`
functions of `OpsShiftMul`:
- `bv_copy_lits_wp`
- `bv_blast_replicate_wp`
- `bv_blast_rotl_wp`
- `bv_blast_rotr_wp`
- `bv_blast_ashrc_wp`
- `bv_blast_reverse_wp`
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Bitblast.Proof

open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofKit
open LeanQbe.T.ProofUtil
open Std.ExtHashMap
open LeanQbe.T.Examples.Bitblast.Src.OpsShiftMul

/-! ## 1. Pure Loop-Step and Post-Closing Helpers -/

private theorem ops_getD_eq_getElem {α : Type _} (xs : List α) (d : α) {i : Nat}
    (hi : i < xs.length) : xs.getD i d = xs[i]'hi := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

private theorem pureOp_bad_decide_false {hdr : BVHdrState} {aOff w : BitVec 32} {capOk : Prop}
    [Decidable capOk] (hbad : hdr.oom ≠ 0#32 ∨ sliceOkBool hdr aOff w = false) :
    decide (hdr.oom = 0#32 ∧ sliceOkBool hdr aOff w = true ∧ capOk) = false := by
  rw [decide_eq_false_iff_not]
  exact fun h => hbad.elim (fun h1 => h1 h.1)
    (fun h1 => Bool.false_ne_true (h1.symm.trans h.2.1))

private theorem pureOp_oom_close {h : BitVec 64} {hdr : BVHdrState}
    {litsPool : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]}
    {ok : BVHdrState → Bool} {outW : BitVec 32} {idxFn : Nat → Nat}
    (hf : ok hdr = false)
    (hm : (bvHdrMem h { hdr with oom := 1#32 } ⋆ array (t := i32) hdr.lits_ptr litsPool ⋆ R) m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr.OpsFrame hdr' → hdr'.aig_len = hdr.aig_len → litsPool'.length = litsPool.length →
      (∀ p < hdr.lits_len.toNat, litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
      (ok hdr = true → hdr'.oom = 0#32 ∧ ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + outW ∧
        ∀ j < outW.toNat, litsPool'.getD (ret.toNat + j) 0#32 = litsPool.getD (idxFn j) 0#32) →
      (ok hdr = false → hdr'.oom = 1#32 ∧ hdr'.lits_len = hdr.lits_len ∧
        ret = 0xFFFFFFFF#32 ∧ litsPool' = litsPool) →
      (bvHdrMem h hdr' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Q (0xFFFFFFFF#32, ⟨⟩) m := by
  have hoom := ops_lits_pure_guard_oom hdr
  exact hQ 0xFFFFFFFF#32 { hdr with oom := 1#32 } litsPool m hoom.2.2.2 hoom.1 rfl
    (fun _ _ => rfl) (fun ht => absurd (hf.symm.trans ht) Bool.false_ne_true)
    (fun _ => ⟨hoom.2.2.1, hoom.2.1, rfl, rfl⟩) hm

private theorem pureOp_ok_close {h : BitVec 64} {hdr : BVHdrState}
    {litsPool lp : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i32]}
    {ok : BVHdrState → Bool} {outW : BitVec 32} {idxFn : Nat → Nat}
    (ht : ok hdr = true) (hoom : hdr.oom = 0#32)
    (hlen : lp.length = litsPool.length)
    (hpre : ∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32)
    (hsl : ∀ j < outW.toNat, lp.getD (hdr.lits_len.toNat + j) 0#32 = litsPool.getD (idxFn j) 0#32)
    (hm : (bvHdrMem h { hdr with lits_len := hdr.lits_len + outW } ⋆
      array (t := i32) hdr.lits_ptr lp ⋆ R) m)
    (hQ : ∀ (ret : BitVec 32) (hdr' : BVHdrState) (litsPool' : List (BitVec 32)) (m' : Mem 64),
      hdr.OpsFrame hdr' → hdr'.aig_len = hdr.aig_len → litsPool'.length = litsPool.length →
      (∀ p < hdr.lits_len.toNat, litsPool'.getD p 0#32 = litsPool.getD p 0#32) →
      (ok hdr = true → hdr'.oom = 0#32 ∧ ret = hdr.lits_len ∧ hdr'.lits_len = hdr.lits_len + outW ∧
        ∀ j < outW.toNat, litsPool'.getD (ret.toNat + j) 0#32 = litsPool.getD (idxFn j) 0#32) →
      (ok hdr = false → hdr'.oom = 1#32 ∧ hdr'.lits_len = hdr.lits_len ∧
        ret = 0xFFFFFFFF#32 ∧ litsPool' = litsPool) →
      (bvHdrMem h hdr' ⋆ array (t := i32) hdr'.lits_ptr litsPool' ⋆ R) m' →
      Q (ret, ⟨⟩) m') :
    Q (hdr.lits_len, ⟨⟩) m :=
  hQ hdr.lits_len { hdr with lits_len := hdr.lits_len + outW } lp m
    (ops_lits_alloc_ok_frame hdr outW) rfl hlen hpre
    (fun _ => ⟨hoom, rfl, rfl, hsl⟩) (fun hf => absurd (hf.symm.trans ht) Bool.false_ne_true) hm

private theorem pureOp_loop_step_val {idxFn : Nat → Nat} {pool0 lp : List (BitVec 32)}
    {litsLen j : Nat} {v : BitVec 32}
    (hlen : lp.length = pool0.length) (hpre : ∀ p < litsLen, lp.getD p 0#32 = pool0.getD p 0#32)
    (hset : ∀ k < j, lp.getD (litsLen + k) 0#32 = pool0.getD (idxFn k) 0#32)
    (hwr : litsLen + j < lp.length) (hv : v = pool0.getD (idxFn j) 0#32) :
    let lp' := lp.set (litsLen + j) v
    lp'.length = pool0.length ∧
    (∀ p < litsLen, lp'.getD p 0#32 = pool0.getD p 0#32) ∧
    (∀ k < j + 1, lp'.getD (litsLen + k) 0#32 = pool0.getD (idxFn k) 0#32) := by
  refine ⟨by simp [hlen], fun p hp => ?_, fun k hk => ?_⟩
  · have hne : litsLen + j ≠ p := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
    exact hpre p hp
  · by_cases hkj : k = j
    · subst hkj
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hwr, Option.getD_some, hv]
    · have hne : litsLen + j ≠ litsLen + k := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
      exact hset k (by omega)

private theorem pureOp_loop_step {idxFn : Nat → Nat} {pool0 lp : List (BitVec 32)}
    {litsLen j srcIdx : Nat}
    (hlen : lp.length = pool0.length) (hpre : ∀ p < litsLen, lp.getD p 0#32 = pool0.getD p 0#32)
    (hset : ∀ k < j, lp.getD (litsLen + k) 0#32 = pool0.getD (idxFn k) 0#32)
    (hwr : litsLen + j < lp.length) (hsrc_bd : srcIdx < litsLen) (hsrc_lt : srcIdx < lp.length)
    (hidx : srcIdx = idxFn j) :
    let lp' := lp.set (litsLen + j) (lp[srcIdx]'hsrc_lt)
    lp'.length = pool0.length ∧
    (∀ p < litsLen, lp'.getD p 0#32 = pool0.getD p 0#32) ∧
    (∀ k < j + 1, lp'.getD (litsLen + k) 0#32 = pool0.getD (idxFn k) 0#32) := by
  have hv : lp[srcIdx]'hsrc_lt = pool0.getD (idxFn j) 0#32 := by
    rw [← ops_getD_eq_getElem lp 0#32 hsrc_lt, hpre srcIdx hsrc_bd, hidx]
  exact pureOp_loop_step_val hlen hpre hset hwr hv

private theorem pureOp_guard_false_alloc {hdr : BVHdrState} {litsPool : List (BitVec 32)}
    {aOff aw count : BitVec 32}
    (hcap : litsPool.length = hdr.lits_cap.toNat)
    (hoom0 : hdr.oom = 0#32) (hsl : sliceOkBool hdr aOff aw = true)
    (hok : count.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) :
    (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
      count.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) ∧
    hdr.lits_len.toNat + count.toNat ≤ litsPool.length := by
  rw [sliceOkBool_true_iff] at hsl
  exact ⟨⟨hoom0, hsl.1, hok⟩, by omega⟩

private theorem pureOp_bv32_succ_add {j : Nat} (hj : j + 1 < 2 ^ 32) :
    BitVec.ofNat 32 j + (1 : BitVec 32) = BitVec.ofNat 32 (j + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]

private theorem bv32_setWidth64_toNat (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := x.isLt; omega)]

private theorem bv32_mul_lt_2p64 (a b : BitVec 32) : a.toNat * b.toNat < 2 ^ 64 :=
  Nat.lt_of_le_of_lt
    (Nat.mul_le_mul (Nat.le_sub_one_of_lt a.isLt) (Nat.le_sub_one_of_lt b.isLt))
    (by decide)

private theorem bv32_setWidth64_mul_toNat (a b : BitVec 32) :
    (a.setWidth 64 * b.setWidth 64).toNat = a.toNat * b.toNat := by
  rw [BitVec.toNat_mul, bv32_setWidth64_toNat, bv32_setWidth64_toNat,
    Nat.mod_eq_of_lt (bv32_mul_lt_2p64 a b)]

/-! ## 3. `bv_copy_lits_wp` -/

public section

theorem bv_copy_lits_wp (Γ : Env) :
    ∀ xs m Q X, bvCopyLitsSpec xs m Q X → Func.wp Γ bv_copy_lits_body xs m Q X := by
  rintro ⟨h, dstOff, srcOff, w, ⟨⟩⟩ m Q X
    ⟨hdr, litsPool, R, hlt, hdst, hsrc, hdisj, hm, hQ⟩
  c0_hfast_nogrp
  refine wp_while_state (α := Nat × List (BitVec 32))
    (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
    (fun (j, lp) ml => j ≤ w.toNat ∧ lp.length = litsPool.length ∧
      (∀ p, p < dstOff.toNat ∨ dstOff.toNat + j ≤ p →
        lp.getD p 0#32 = litsPool.getD p 0#32) ∧
      (∀ k < j, lp.getD (dstOff.toNat + k) 0#32 = litsPool.getD (srcOff.toNat + k) 0#32) ∧
      (bvHdrMem h hdr ⋆ array (t := i32) hdr.lits_ptr lp ⋆ R) ml) ?_ ?_
  · intro J hJ
    c0_hsteps
    exact hJ (0, litsPool) m ⟨Nat.zero_le _, rfl, fun _ _ => rfl, fun _ hk => by omega, hm⟩
  · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hout, hin, hml⟩ ih
    c0_hstraight; c0_hsplit
    · have hj_lt : j < w.toNat := by
        have h1 : BitVec.ofNat 32 j < w := hc
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
        exact h1
      clear hc
      have hj32 : (BitVec.ofNat 32 j).toNat = j := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hsrc_idx : (srcOff + BitVec.ofNat 32 j).toNat = srcOff.toNat + j := by
        rw [BitVec.toNat_add, hj32, Nat.mod_eq_of_lt (by omega)]
      have hdst_idx : (dstOff + BitVec.ofNat 32 j).toNat = dstOff.toNat + j := by
        rw [BitVec.toNat_add, hj32, Nat.mod_eq_of_lt (by omega)]
      have hsrc_sw : ((srcOff + BitVec.ofNat 32 j).setWidth 64).toNat = srcOff.toNat + j := by
        rw [bv32_setWidth64_toNat, hsrc_idx]
      have hdst_sw : ((dstOff + BitVec.ofNat 32 j).setWidth 64).toNat = dstOff.toNat + j := by
        rw [bv32_setWidth64_toNat, hdst_idx]
      have hsrc_agree : lp[((srcOff + BitVec.ofNat 32 j).setWidth 64).toNat]'(by
            rw [hsrc_sw, hlp_len]; omega) = litsPool.getD (srcOff.toNat + j) 0#32 := by
        rw [← ops_getD_eq_getElem lp 0#32 (by rw [hsrc_sw, hlp_len]; omega), hsrc_sw]
        exact hout _ (by omega)
      c0_hstraight
      rw [pureOp_bv32_succ_add (by omega)]
      let lp' := lp.set ((dstOff + BitVec.ofNat 32 j).setWidth 64).toNat
        (lp[((srcOff + BitVec.ofNat 32 j).setWidth 64).toNat]'(by rw [hsrc_sw, hlp_len]; omega))
      refine ih (j + 1, lp') _ (by dsimp only; omega)
        ⟨by omega, by simp [lp', hlp_len], ?_, ?_, sep_ac hm⟩
      · intro p hp
        have hne : ((dstOff + BitVec.ofNat 32 j).setWidth 64).toNat ≠ p := by rw [hdst_sw]; omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
        exact hout p (by omega)
      · intro k hk
        by_cases hkj : k = j
        · subst hkj
          have hdst_lt : ((dstOff + BitVec.ofNat 32 k).setWidth 64).toNat < lp.length := by
            rw [hdst_sw, hlp_len]; omega
          rw [← hdst_sw, List.getD_eq_getElem?_getD, List.getElem?_set_self hdst_lt,
            Option.getD_some, hsrc_agree]
        · have hne : ((dstOff + BitVec.ofNat 32 j).setWidth 64).toNat ≠ dstOff.toNat + k := by
            rw [hdst_sw]; omega
          rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
          exact hin k (by omega)
    · have hj_eq : j = w.toNat := by
        have h1 : ¬ BitVec.ofNat 32 j < w := hc
        rw [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
        omega
      clear hc
      c0_hsteps
      exact hQ lp ml hlp_len (hj_eq ▸ hout) (hj_eq ▸ hin) hml

/-! ## 4. `bv_blast_replicate_wp` -/

theorem bv_blast_replicate_wp (Γ : Env)
    (hSlice : Γ.Has "bv_slice_ok" smBvSliceOkSpec)
    (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec)
    (hCopy : Γ.Has "bv_copy_lits" bvCopyLitsSpec) :
    ∀ xs m Q X, bvBlastReplicateSpec xs m Q X → Func.wp Γ bv_blast_replicate_body xs m Q X := by
  rintro ⟨h, aOff, aw, n, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hcap, hm, hQ⟩
  let okFn : BVHdrState → Bool := fun hd =>
    decide (hd.oom = 0#32 ∧ sliceOkBool hd aOff aw = true ∧
      aw.toNat * n.toNat ≤ hd.lits_cap.toNat - hd.lits_len.toNat)
  c0_hstraight
  refine wp_join0 (fun m_bad => m_bad = m ∧ (hdr.oom ≠ 0#32 ∨ sliceOkBool hdr aOff aw = false))
    ?_ ?_
  · intro _ m_bad ⟨hm_bad, hbad⟩; subst hm_bad
    c0_hsteps
    exact pureOp_oom_close (ok := okFn) (pureOp_bad_decide_false hbad) (sep_ac hm) hQ
  · intro J_bad hJ_bad
    c0_hstraight; c0_hsplit
    · exact hJ_bad m ⟨rfl, Or.inl (by c0_bv_omega [hc])⟩
    have hoom0 : hdr.oom = 0#32 := by c0_bv_omega [hc]
    clear hc; c0_hstraight
    c0_hcall hSlice; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
    c0_hsplit
    · have hsl_t : sliceOkBool hdr aOff aw = true := by
        cases hok : sliceOkBool hdr aOff aw <;> simp_all
      clear hc hJ_bad; c0_hstraight; c0_hsplit
      · have hgt : aw.toNat * n.toNat > 0xFFFFFFFF := by
          have htot := bv32_setWidth64_mul_toNat aw n
          c0_bv_omega [hc, htot]
        have hfail : okFn hdr = false := by
          simp only [okFn, decide_eq_false_iff_not, not_and]
          intro _ _ hle; have := hdr.lits_cap.isLt; omega
        clear hc; c0_hsteps
        exact pureOp_oom_close (ok := okFn) hfail (sep_ac hm) hQ
      have hle32 : aw.toNat * n.toNat ≤ 0xFFFFFFFF := by
        have htot := bv32_setWidth64_mul_toNat aw n
        c0_bv_omega [hc, htot]
      have hcnt_eq : (aw.setWidth 64 * n.setWidth 64).setWidth 32 =
          BitVec.ofNat 32 (aw.toNat * n.toNat) := by
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_setWidth, bv32_setWidth64_mul_toNat, BitVec.toNat_ofNat]
      have hcnt_toNat : (BitVec.ofNat 32 (aw.toNat * n.toNat)).toNat = aw.toNat * n.toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      clear hc; c0_hstraight; rw [hcnt_eq]
      c0_hcall hAlloc; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
      by_cases hfit : aw.toNat * n.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat
      · have ⟨hcond, hbd_all⟩ := pureOp_guard_false_alloc hcap hoom0 hsl_t (hcnt_toNat ▸ hfit)
        rw [ite_eq_left hcond]; intro m1 hm1
        have hok_t : okFn hdr = true := by simp [okFn, hoom0, hsl_t, hfit]
        let outW := BitVec.ofNat 32 (aw.toNat * n.toNat)
        let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + outW }
        c0_hstraight; c0_hsplit
        · exfalso; exact hc hoom0
        · clear hc; c0_hstraight
          refine wp_join0 (fun m2 => ∃ lp' : List (BitVec 32),
            lp'.length = litsPool.length ∧
            (∀ p < hdr.lits_len.toNat, lp'.getD p 0#32 = litsPool.getD p 0#32) ∧
            (∀ j < outW.toNat, lp'.getD (hdr.lits_len.toNat + j) 0#32 =
              litsPool.getD (aOff.toNat + j % aw.toNat) 0#32) ∧
            (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp' ⋆ R) m2) ?_ ?_
          · intro _ m2 ⟨lp', hlen', hpre', hin', hm2⟩
            c0_hsteps
            dsimp only [hdr1] at hm2
            exact pureOp_ok_close (ok := okFn) hok_t hoom0 hlen' hpre' hin' (sep_ac hm2) hQ
          · intro J_skip hJ_skip
            c0_hstraight; c0_hsplit
            · have haw_pos : 0 < aw.toNat := by c0_bv_omega [hc]
              clear hc; c0_hstraight; c0_hsplit
              · have hn_pos : 0 < n.toNat := by c0_bv_omega [hc]
                clear hc
                refine wp_while_state (α := Nat × List (BitVec 32))
                  (fun (k, _) => (BitVec.ofNat 32 k, ())) (fun (k, _) => n.toNat - k)
                  (fun (k, lp) ml => k ≤ n.toNat ∧ lp.length = litsPool.length ∧
                    (∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32) ∧
                    (∀ j < k * aw.toNat,
                      lp.getD (hdr.lits_len.toNat + j) 0#32 =
                        litsPool.getD (aOff.toNat + j % aw.toNat) 0#32) ∧
                    (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp ⋆ R) ml) ?_ ?_
                · intro J hJ; c0_hsteps
                  exact hJ (0, litsPool) m1
                    ⟨Nat.zero_le _, rfl, fun _ _ => rfl, fun _ hj => by omega, sep_ac hm1⟩
                · intro J ⟨k, lp⟩ ml ⟨hk_le, hlp_len, hpre, hin, hml⟩ ih
                  c0_hstraight; c0_hsplit
                  · have hk_lt : k < n.toNat := by
                      have h1 : BitVec.ofNat 32 k < n := hc
                      rw [BitVec.lt_def, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by have := n.isLt; omega)] at h1
                      exact h1
                    clear hc
                    have hk32 : (BitVec.ofNat 32 k).toNat = k := by
                      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := n.isLt; omega)]
                    have hk_aw_lt : k * aw.toNat + aw.toNat ≤ aw.toNat * n.toNat := by
                      have : (k + 1) * aw.toNat ≤ n.toNat * aw.toNat :=
                        Nat.mul_le_mul_right _ hk_lt
                      rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm n.toNat aw.toNat] at this
                      exact this
                    have hsl' := hsl_t; rw [sliceOkBool_true_iff] at hsl'
                    have hdst_toNat : (hdr.lits_len + BitVec.ofNat 32 k * aw).toNat =
                        hdr.lits_len.toNat + k * aw.toNat := by
                      rw [BitVec.toNat_add, BitVec.toNat_mul, hk32,
                        Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
                    c0_hstraight
                    c0_hcall hCopy
                    refine ⟨hdr1, lp, R, by rw [hlp_len, hcap]; exact hdr.lits_cap.isLt,
                      by rw [hdst_toNat, hlp_len]; omega,
                      by rw [hlp_len]; omega,
                      Or.inr (by rw [hdst_toNat]; omega), sep_ac hml,
                      fun lp' m2 hlp'_len hout' hin' hm2 => ?_⟩
                    c0_hstraight
                    rw [pureOp_bv32_succ_add (by have := n.isLt; omega)]
                    refine ih (k + 1, lp') m2 (by dsimp only; omega)
                      ⟨by omega, hlp'_len.trans hlp_len, fun p hp => ?_, fun j hj => ?_, sep_ac hm2⟩
                    · rw [hout' p (Or.inl (by rw [hdst_toNat]; omega)), hpre p hp]
                    · by_cases hjk : j < k * aw.toNat
                      · rw [hout' _ (Or.inl (by rw [hdst_toNat]; omega)), hin j hjk]
                      · have hge : k * aw.toNat ≤ j := Nat.le_of_not_lt hjk
                        have hj1 : j < (k + 1) * aw.toNat := hj
                        have hj_lt : j - k * aw.toNat < aw.toNat := by
                          rw [Nat.add_mul, Nat.one_mul] at hj1; omega
                        have hplus : hdr.lits_len.toNat + j =
                            (hdr.lits_len + BitVec.ofNat 32 k * aw).toNat +
                              (j - k * aw.toNat) := by
                          rw [hdst_toNat]; omega
                        have hmod : j % aw.toNat = j - k * aw.toNat := by
                          have hsp : j = (j - k * aw.toNat) + aw.toNat * k := by
                            rw [Nat.mul_comm aw.toNat k]; omega
                          conv => lhs; rw [hsp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj_lt]
                        rw [hplus, hin' _ hj_lt, hpre _ (by omega), hmod]
                  · have hk_eq : k = n.toNat := by
                      have h1 : ¬ BitVec.ofNat 32 k < n := hc
                      rw [BitVec.lt_def, BitVec.toNat_ofNat,
                        Nat.mod_eq_of_lt (by have := n.isLt; omega)] at h1
                      omega
                    clear hc
                    have hmul : k * aw.toNat = outW.toNat := by
                      rw [hk_eq, Nat.mul_comm, hcnt_toNat]
                    exact hJ_skip ml ⟨lp, hlp_len, hpre,
                      fun j hj => hin j (hmul.symm ▸ hj), hml⟩
              · have hn0 : n.toNat = 0 := by c0_bv_omega [hc]
                exact hJ_skip m1 ⟨litsPool, rfl, fun _ _ => rfl,
                  (fun j hj => by rw [hcnt_toNat, hn0, Nat.mul_zero] at hj; cases hj), sep_ac hm1⟩
            · have haw0 : aw.toNat = 0 := by c0_bv_omega [hc]
              exact hJ_skip m1 ⟨litsPool, rfl, fun _ _ => rfl,
                (fun j hj => by rw [hcnt_toNat, haw0, Nat.zero_mul] at hj; cases hj), sep_ac hm1⟩
      · have hcond : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
            (BitVec.ofNat 32 (aw.toNat * n.toNat)).toNat ≤
              hdr.lits_cap.toNat - hdr.lits_len.toNat) := by
          rw [hcnt_toNat]; intro h; exact hfit h.2.2
        rw [ite_eq_right hcond]; dsimp only; rw [ite_eq_right (fun h => h hoom0)]
        intro m1 hm1
        have hfail : okFn hdr = false := by simp [okFn, hoom0, hsl_t, hfit]
        c0_hstraight; c0_hsplit
        · clear hc; c0_hsteps; exact pureOp_oom_close (ok := okFn) hfail (sep_ac hm1) hQ
        · exfalso; cases hc
    · exact hJ_bad m ⟨rfl, Or.inr (by cases hok : sliceOkBool hdr aOff aw <;> simp_all)⟩

/-! ## 5. `bv_blast_rotl_wp`, `bv_blast_rotr_wp`, `bv_blast_ashrc_wp`, `bv_blast_reverse_wp` -/

theorem bv_blast_rotl_wp (Γ : Env)
    (hSlice : Γ.Has "bv_slice_ok" smBvSliceOkSpec)
    (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec) :
    ∀ xs m Q X, bvBlastRotlSpec xs m Q X → Func.wp Γ bv_blast_rotl_body xs m Q X := by
  rintro ⟨h, aOff, w, n, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hcap, hm, hQ⟩
  let okFn : BVHdrState → Bool := fun hd =>
    decide (hd.oom = 0#32 ∧ sliceOkBool hd aOff w = true ∧
      w.toNat ≤ hd.lits_cap.toNat - hd.lits_len.toNat)
  let idxFn : Nat → Nat := fun j =>
    let r := n.toNat % w.toNat
    aOff.toNat + (if j < r then w.toNat - r + j else j - r)
  c0_hstraight
  refine wp_join0 (fun m_bad => m_bad = m ∧ (hdr.oom ≠ 0#32 ∨ sliceOkBool hdr aOff w = false))
    ?_ ?_
  · intro _ m_bad ⟨hm_bad, hbad⟩; subst hm_bad
    c0_hsteps
    exact pureOp_oom_close (ok := okFn) (pureOp_bad_decide_false hbad) (sep_ac hm) hQ
  · intro J_bad hJ_bad
    c0_hstraight; c0_hsplit
    · exact hJ_bad m ⟨rfl, Or.inl (by c0_bv_omega [hc])⟩
    have hoom0 : hdr.oom = 0#32 := by c0_bv_omega [hc]
    clear hc; c0_hstraight
    c0_hcall hSlice; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
    c0_hsplit
    · have hsl_t : sliceOkBool hdr aOff w = true := by
        cases hok : sliceOkBool hdr aOff w <;> simp_all
      clear hc hJ_bad; c0_hstraight
      c0_hcall hAlloc; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
      by_cases hfit : w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat
      · have ⟨hcond, hbd_all⟩ := pureOp_guard_false_alloc hcap hoom0 hsl_t hfit
        rw [ite_eq_left hcond]; intro m1 hm1
        have hok_t : okFn hdr = true := by simp [okFn, hoom0, hsl_t, hfit]
        let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + w }
        c0_hstraight; c0_hsplit
        · exfalso; exact hc hoom0
        · clear hc; c0_hstraight; c0_hsplit
          · have hw0 : w = 0#32 := by c0_bv_omega [hc]
            clear hc; c0_hsteps
            exact pureOp_ok_close (ok := okFn) hok_t hoom0 rfl (fun _ _ => rfl)
              (fun j hj => by rw [hw0] at hj; simp at hj) (sep_ac hm1) hQ
          · have hw_pos : 0 < w.toNat := by c0_bv_omega [hc]
            clear hc
            have hsl' := hsl_t; rw [sliceOkBool_true_iff] at hsl'
            have hr_lt : n.toNat % w.toNat < w.toNat := Nat.mod_lt _ hw_pos
            have hr_eq : (n % w).toNat = n.toNat % w.toNat := by rw [BitVec.toNat_umod]
            c0_hstraight
            refine wp_while_state (α := Nat × List (BitVec 32))
              (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
              (fun (j, lp) ml => j ≤ w.toNat ∧ lp.length = litsPool.length ∧
                (∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32) ∧
                (∀ k < j, lp.getD (hdr.lits_len.toNat + k) 0#32 = litsPool.getD (idxFn k) 0#32) ∧
                (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp ⋆ R) ml) ?_ ?_
            · intro J hJ; c0_hsteps
              change (bvHdrMem h hdr1 ⋆ (array (t := i32) hdr1.lits_ptr litsPool ⋆ R)) m1 at hm1
              exact hJ (0, litsPool) m1
                ⟨Nat.zero_le _, rfl, fun _ _ => rfl, fun _ hk => by omega, sep_ac hm1⟩
            · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hpre, hin, hml⟩ ih
              c0_hstraight; c0_hsplit
              · have hj_lt : j < w.toNat := by
                  have h1 : BitVec.ofNat 32 j < w := hc
                  rw [BitVec.lt_def, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by have := w.isLt; omega)] at h1
                  exact h1
                clear hc
                have hj32 : (BitVec.ofNat 32 j).toNat = j := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                have hout_sw :
                    ((hdr.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
                    hdr.lits_len.toNat + j := by
                  rw [bv32_setWidth64_toNat, BitVec.toNat_add, hj32, Nat.mod_eq_of_lt (by omega)]
                c0_hstraight
                refine wp_join0 (fun m2 => ∃ lp' : List (BitVec 32),
                  lp'.length = litsPool.length ∧
                  (∀ p < hdr.lits_len.toNat, lp'.getD p 0#32 = litsPool.getD p 0#32) ∧
                  (∀ k < j + 1,
                    lp'.getD (hdr.lits_len.toNat + k) 0#32 = litsPool.getD (idxFn k) 0#32) ∧
                  (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp' ⋆ R) m2) ?_ ?_
                · intro _ m2 ⟨lp', hlen', hpre', hin', hm2⟩
                  c0_hsteps
                  rw [pureOp_bv32_succ_add (by have := w.isLt; omega)]
                  exact ih (j + 1, lp') m2 (by dsimp only; omega)
                    ⟨by omega, hlen', hpre', hin', hm2⟩
                · intro J_if hJ_if
                  c0_hstraight; c0_hsplit
                  · have hjr : j < n.toNat % w.toNat := by
                      have h1 : BitVec.ofNat 32 j < n % w := hc
                      rw [BitVec.lt_def, hj32, hr_eq] at h1; exact h1
                    clear hc
                    have hsrc_sw :
                        ((aOff + (w - n % w + BitVec.ofNat 32 j)).setWidth 64).toNat =
                        aOff.toNat + (w.toNat - n.toNat % w.toNat + j) := by
                      have hw1 : (w - n % w + BitVec.ofNat 32 j).toNat =
                          w.toNat - n.toNat % w.toNat + j := by
                        rw [BitVec.toNat_add, BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)),
                          hr_eq, hj32, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                      rw [bv32_setWidth64_toNat, BitVec.toNat_add, hw1, Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps
                    have hstep := pureOp_loop_step (idxFn := idxFn)
                      (srcIdx := ((aOff + (w - n % w + BitVec.ofNat 32 j)).setWidth 64).toNat)
                      hlp_len hpre hin (by rw [hlp_len]; omega) (by rw [hsrc_sw]; omega)
                      (by rw [hsrc_sw, hlp_len]; omega)
                      (by rw [hsrc_sw]; simp only [idxFn, hjr, ↓reduceIte])
                    rw [hout_sw] at *
                    exact hJ_if _ ⟨_, hstep.1, hstep.2.1, hstep.2.2, sep_ac hm⟩
                  · have hjr : ¬ j < n.toNat % w.toNat := by
                      have h1 : ¬ BitVec.ofNat 32 j < n % w := hc
                      rw [BitVec.lt_def, hj32, hr_eq] at h1; exact h1
                    clear hc
                    have hsrc_sw :
                        ((aOff + (BitVec.ofNat 32 j - n % w)).setWidth 64).toNat =
                        aOff.toNat + (j - n.toNat % w.toNat) := by
                      have hj1 : (BitVec.ofNat 32 j - n % w).toNat = j - n.toNat % w.toNat := by
                        rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hj32, hr_eq]; omega)),
                          hj32, hr_eq]
                      rw [bv32_setWidth64_toNat, BitVec.toNat_add, hj1, Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps
                    have hstep := pureOp_loop_step (idxFn := idxFn)
                      (srcIdx := ((aOff + (BitVec.ofNat 32 j - n % w)).setWidth 64).toNat)
                      hlp_len hpre hin (by rw [hlp_len]; omega) (by rw [hsrc_sw]; omega)
                      (by rw [hsrc_sw, hlp_len]; omega)
                      (by rw [hsrc_sw]; simp only [idxFn, ite_eq_right hjr])
                    rw [hout_sw] at *
                    exact hJ_if _ ⟨_, hstep.1, hstep.2.1, hstep.2.2, sep_ac hm⟩
              · have hj_eq : j = w.toNat := by
                  have h1 : ¬ BitVec.ofNat 32 j < w := hc
                  rw [BitVec.lt_def, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by have := w.isLt; omega)] at h1
                  omega
                clear hc; c0_hsteps
                exact pureOp_ok_close (ok := okFn) hok_t hoom0 hlp_len hpre
                  (fun k hk => hin k (hj_eq ▸ hk)) hml hQ
      · have hcond : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
            w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) := fun h => hfit h.2.2
        rw [ite_eq_right hcond]; dsimp only; rw [ite_eq_right (fun h => h hoom0)]
        intro m1 hm1
        have hfail : okFn hdr = false := by simp [okFn, hoom0, hsl_t, hfit]
        c0_hstraight; c0_hsplit
        · clear hc; c0_hsteps; exact pureOp_oom_close (ok := okFn) hfail (sep_ac hm1) hQ
        · exfalso; cases hc
    · exact hJ_bad m ⟨rfl, Or.inr (by cases hok : sliceOkBool hdr aOff w <;> simp_all)⟩

theorem bv_blast_rotr_wp (Γ : Env)
    (hSlice : Γ.Has "bv_slice_ok" smBvSliceOkSpec)
    (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec) :
    ∀ xs m Q X, bvBlastRotrSpec xs m Q X → Func.wp Γ bv_blast_rotr_body xs m Q X := by
  rintro ⟨h, aOff, w, n, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hcap, hm, hQ⟩
  let okFn : BVHdrState → Bool := fun hd =>
    decide (hd.oom = 0#32 ∧ sliceOkBool hd aOff w = true ∧
      w.toNat ≤ hd.lits_cap.toNat - hd.lits_len.toNat)
  let idxFn : Nat → Nat := fun j =>
    let r := n.toNat % w.toNat
    let cut := w.toNat - r
    aOff.toNat + (if j < cut then r + j else j - cut)
  c0_hstraight
  refine wp_join0 (fun m_bad => m_bad = m ∧ (hdr.oom ≠ 0#32 ∨ sliceOkBool hdr aOff w = false))
    ?_ ?_
  · intro _ m_bad ⟨hm_bad, hbad⟩; subst hm_bad
    c0_hsteps
    exact pureOp_oom_close (ok := okFn) (pureOp_bad_decide_false hbad) (sep_ac hm) hQ
  · intro J_bad hJ_bad
    c0_hstraight; c0_hsplit
    · exact hJ_bad m ⟨rfl, Or.inl (by c0_bv_omega [hc])⟩
    have hoom0 : hdr.oom = 0#32 := by c0_bv_omega [hc]
    clear hc; c0_hstraight
    c0_hcall hSlice; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
    c0_hsplit
    · have hsl_t : sliceOkBool hdr aOff w = true := by
        cases hok : sliceOkBool hdr aOff w <;> simp_all
      clear hc hJ_bad; c0_hstraight
      c0_hcall hAlloc; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
      by_cases hfit : w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat
      · have ⟨hcond, hbd_all⟩ := pureOp_guard_false_alloc hcap hoom0 hsl_t hfit
        rw [ite_eq_left hcond]; intro m1 hm1
        have hok_t : okFn hdr = true := by simp [okFn, hoom0, hsl_t, hfit]
        let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + w }
        c0_hstraight; c0_hsplit
        · exfalso; exact hc hoom0
        · clear hc; c0_hstraight; c0_hsplit
          · have hw0 : w = 0#32 := by c0_bv_omega [hc]
            clear hc; c0_hsteps
            exact pureOp_ok_close (ok := okFn) hok_t hoom0 rfl (fun _ _ => rfl)
              (fun j hj => by rw [hw0] at hj; simp at hj) (sep_ac hm1) hQ
          · have hw_pos : 0 < w.toNat := by c0_bv_omega [hc]
            clear hc
            have hsl' := hsl_t; rw [sliceOkBool_true_iff] at hsl'
            have hr_lt : n.toNat % w.toNat < w.toNat := Nat.mod_lt _ hw_pos
            have hr_eq : (n % w).toNat = n.toNat % w.toNat := by rw [BitVec.toNat_umod]
            have hcut_eq : (w - n % w).toNat = w.toNat - n.toNat % w.toNat := by
              rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega)), hr_eq]
            c0_hstraight
            refine wp_while_state (α := Nat × List (BitVec 32))
              (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
              (fun (j, lp) ml => j ≤ w.toNat ∧ lp.length = litsPool.length ∧
                (∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32) ∧
                (∀ k < j, lp.getD (hdr.lits_len.toNat + k) 0#32 = litsPool.getD (idxFn k) 0#32) ∧
                (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp ⋆ R) ml) ?_ ?_
            · intro J hJ; c0_hsteps
              change (bvHdrMem h hdr1 ⋆ (array (t := i32) hdr1.lits_ptr litsPool ⋆ R)) m1 at hm1
              exact hJ (0, litsPool) m1
                ⟨Nat.zero_le _, rfl, fun _ _ => rfl, fun _ hk => by omega, sep_ac hm1⟩
            · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hpre, hin, hml⟩ ih
              c0_hstraight; c0_hsplit
              · have hj_lt : j < w.toNat := by
                  have h1 : BitVec.ofNat 32 j < w := hc
                  rw [BitVec.lt_def, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by have := w.isLt; omega)] at h1
                  exact h1
                clear hc
                have hj32 : (BitVec.ofNat 32 j).toNat = j := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                have hout_sw :
                    ((hdr.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
                    hdr.lits_len.toNat + j := by
                  rw [bv32_setWidth64_toNat, BitVec.toNat_add, hj32, Nat.mod_eq_of_lt (by omega)]
                c0_hstraight
                refine wp_join0 (fun m2 => ∃ lp' : List (BitVec 32),
                  lp'.length = litsPool.length ∧
                  (∀ p < hdr.lits_len.toNat, lp'.getD p 0#32 = litsPool.getD p 0#32) ∧
                  (∀ k < j + 1,
                    lp'.getD (hdr.lits_len.toNat + k) 0#32 = litsPool.getD (idxFn k) 0#32) ∧
                  (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp' ⋆ R) m2) ?_ ?_
                · intro _ m2 ⟨lp', hlen', hpre', hin', hm2⟩
                  c0_hsteps
                  rw [pureOp_bv32_succ_add (by have := w.isLt; omega)]
                  exact ih (j + 1, lp') m2 (by dsimp only; omega)
                    ⟨by omega, hlen', hpre', hin', hm2⟩
                · intro J_if hJ_if
                  c0_hstraight; c0_hsplit
                  · have hjc : j < w.toNat - n.toNat % w.toNat := by
                      have h1 : BitVec.ofNat 32 j < w - n % w := hc
                      rw [BitVec.lt_def, hj32, hcut_eq] at h1; exact h1
                    clear hc
                    have hsrc_sw :
                        ((aOff + (n % w + BitVec.ofNat 32 j)).setWidth 64).toNat =
                        aOff.toNat + (n.toNat % w.toNat + j) := by
                      have hj1 : (n % w + BitVec.ofNat 32 j).toNat = n.toNat % w.toNat + j := by
                        rw [BitVec.toNat_add, hr_eq, hj32,
                          Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                      rw [bv32_setWidth64_toNat, BitVec.toNat_add, hj1, Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps
                    have hstep := pureOp_loop_step (idxFn := idxFn)
                      (srcIdx := ((aOff + (n % w + BitVec.ofNat 32 j)).setWidth 64).toNat)
                      hlp_len hpre hin (by rw [hlp_len]; omega) (by rw [hsrc_sw]; omega)
                      (by rw [hsrc_sw, hlp_len]; omega)
                      (by rw [hsrc_sw]; simp only [idxFn, hjc, ↓reduceIte])
                    rw [hout_sw] at *
                    exact hJ_if _ ⟨_, hstep.1, hstep.2.1, hstep.2.2, sep_ac hm⟩
                  · have hjc : ¬ j < w.toNat - n.toNat % w.toNat := by
                      have h1 : ¬ BitVec.ofNat 32 j < w - n % w := hc
                      rw [BitVec.lt_def, hj32, hcut_eq] at h1; exact h1
                    clear hc
                    have hsrc_sw :
                        ((aOff + (BitVec.ofNat 32 j - (w - n % w))).setWidth 64).toNat =
                        aOff.toNat + (j - (w.toNat - n.toNat % w.toNat)) := by
                      have hj1 : (BitVec.ofNat 32 j - (w - n % w)).toNat =
                          j - (w.toNat - n.toNat % w.toNat) := by
                        have hle : w - n % w ≤ BitVec.ofNat 32 j :=
                          BitVec.le_def.mpr (by rw [hj32, hcut_eq]; omega)
                        rw [BitVec.toNat_sub_of_le hle, hj32, hcut_eq]
                      rw [bv32_setWidth64_toNat, BitVec.toNat_add, hj1, Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps
                    have hstep := pureOp_loop_step (idxFn := idxFn)
                      (srcIdx :=
                        ((aOff + (BitVec.ofNat 32 j - (w - n % w))).setWidth 64).toNat)
                      hlp_len hpre hin (by rw [hlp_len]; omega) (by rw [hsrc_sw]; omega)
                      (by rw [hsrc_sw, hlp_len]; omega)
                      (by rw [hsrc_sw]; simp only [idxFn, ite_eq_right hjc])
                    rw [hout_sw] at *
                    exact hJ_if _ ⟨_, hstep.1, hstep.2.1, hstep.2.2, sep_ac hm⟩
              · have hj_eq : j = w.toNat := by
                  have h1 : ¬ BitVec.ofNat 32 j < w := hc
                  rw [BitVec.lt_def, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by have := w.isLt; omega)] at h1
                  omega
                clear hc; c0_hsteps
                exact pureOp_ok_close (ok := okFn) hok_t hoom0 hlp_len hpre
                  (fun k hk => hin k (hj_eq ▸ hk)) hml hQ
      · have hcond : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
            w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) := fun h => hfit h.2.2
        rw [ite_eq_right hcond]; dsimp only; rw [ite_eq_right (fun h => h hoom0)]
        intro m1 hm1
        have hfail : okFn hdr = false := by simp [okFn, hoom0, hsl_t, hfit]
        c0_hstraight; c0_hsplit
        · clear hc; c0_hsteps; exact pureOp_oom_close (ok := okFn) hfail (sep_ac hm1) hQ
        · exfalso; cases hc
    · exact hJ_bad m ⟨rfl, Or.inr (by cases hok : sliceOkBool hdr aOff w <;> simp_all)⟩

theorem bv_blast_ashrc_wp (Γ : Env)
    (hSlice : Γ.Has "bv_slice_ok" smBvSliceOkSpec)
    (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec) :
    ∀ xs m Q X, bvBlastAshrcSpec xs m Q X → Func.wp Γ bv_blast_ashrc_body xs m Q X := by
  rintro ⟨h, aOff, w, n, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hcap, hm, hQ⟩
  let okFn : BVHdrState → Bool := fun hd =>
    decide (hd.oom = 0#32 ∧ sliceOkBool hd aOff w = true ∧
      w.toNat ≤ hd.lits_cap.toNat - hd.lits_len.toNat)
  let idxFn : Nat → Nat := fun j =>
    aOff.toNat + (if n.toNat + j < w.toNat then n.toNat + j else w.toNat - 1)
  c0_hstraight
  refine wp_join0 (fun m_bad => m_bad = m ∧ (hdr.oom ≠ 0#32 ∨ sliceOkBool hdr aOff w = false))
    ?_ ?_
  · intro _ m_bad ⟨hm_bad, hbad⟩; subst hm_bad
    c0_hsteps
    exact pureOp_oom_close (ok := okFn) (pureOp_bad_decide_false hbad) (sep_ac hm) hQ
  · intro J_bad hJ_bad
    c0_hstraight; c0_hsplit
    · exact hJ_bad m ⟨rfl, Or.inl (by c0_bv_omega [hc])⟩
    have hoom0 : hdr.oom = 0#32 := by c0_bv_omega [hc]
    clear hc; c0_hstraight
    c0_hcall hSlice; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
    c0_hsplit
    · have hsl_t : sliceOkBool hdr aOff w = true := by
        cases hok : sliceOkBool hdr aOff w <;> simp_all
      clear hc hJ_bad; c0_hstraight
      c0_hcall hAlloc; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
      by_cases hfit : w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat
      · have ⟨hcond, hbd_all⟩ := pureOp_guard_false_alloc hcap hoom0 hsl_t hfit
        rw [ite_eq_left hcond]; intro m1 hm1
        have hok_t : okFn hdr = true := by simp [okFn, hoom0, hsl_t, hfit]
        let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + w }
        c0_hstraight; c0_hsplit
        · exfalso; exact hc hoom0
        · clear hc; c0_hstraight; c0_hsplit
          · have hw0 : w = 0#32 := by c0_bv_omega [hc]
            clear hc; c0_hsteps
            exact pureOp_ok_close (ok := okFn) hok_t hoom0 rfl (fun _ _ => rfl)
              (fun j hj => by rw [hw0] at hj; simp at hj) (sep_ac hm1) hQ
          · have hw_pos : 0 < w.toNat := by c0_bv_omega [hc]
            clear hc
            have hsl' := hsl_t; rw [sliceOkBool_true_iff] at hsl'
            have hsign_sw : ((aOff + (w - 1#32)).setWidth 64).toNat =
                aOff.toNat + (w.toNat - 1) := by
              have hw1 : (w - 1#32).toNat = w.toNat - 1 := by
                rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
                  (by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega))]; rfl
              rw [bv32_setWidth64_toNat, BitVec.toNat_add, hw1, Nat.mod_eq_of_lt (by omega)]
            c0_hstraight
            refine wp_while_state (α := Nat × List (BitVec 32))
              (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
              (fun (j, lp) ml => j ≤ w.toNat ∧ lp.length = litsPool.length ∧
                (∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32) ∧
                (∀ k < j, lp.getD (hdr.lits_len.toNat + k) 0#32 = litsPool.getD (idxFn k) 0#32) ∧
                (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp ⋆ R) ml) ?_ ?_
            · intro J hJ; c0_hsteps
              change (bvHdrMem h hdr1 ⋆ (array (t := i32) hdr1.lits_ptr litsPool ⋆ R)) m1 at hm1
              exact hJ (0, litsPool) m1
                ⟨Nat.zero_le _, rfl, fun _ _ => rfl, fun _ hk => by omega, sep_ac hm1⟩
            · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hpre, hin, hml⟩ ih
              c0_hstraight; c0_hsplit
              · have hj_lt : j < w.toNat := by
                  have h1 : BitVec.ofNat 32 j < w := hc
                  rw [BitVec.lt_def, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by have := w.isLt; omega)] at h1
                  exact h1
                clear hc
                have hj32 : (BitVec.ofNat 32 j).toNat = j := by
                  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                have hout_sw :
                    ((hdr.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
                    hdr.lits_len.toNat + j := by
                  rw [bv32_setWidth64_toNat, BitVec.toNat_add, hj32, Nat.mod_eq_of_lt (by omega)]
                have hpos_toNat : (n.setWidth 64 + (BitVec.ofNat 32 j).setWidth 64).toNat =
                    n.toNat + j := by
                  rw [BitVec.toNat_add, bv32_setWidth64_toNat, bv32_setWidth64_toNat, hj32,
                    Nat.mod_eq_of_lt (by have := n.isLt; have := w.isLt; omega)]
                c0_hstraight
                refine wp_join0 (fun m2 => ∃ lp' : List (BitVec 32),
                  lp'.length = litsPool.length ∧
                  (∀ p < hdr.lits_len.toNat, lp'.getD p 0#32 = litsPool.getD p 0#32) ∧
                  (∀ k < j + 1,
                    lp'.getD (hdr.lits_len.toNat + k) 0#32 = litsPool.getD (idxFn k) 0#32) ∧
                  (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp' ⋆ R) m2) ?_ ?_
                · intro _ m2 ⟨lp', hlen', hpre', hin', hm2⟩
                  c0_hsteps
                  rw [pureOp_bv32_succ_add (by have := w.isLt; omega)]
                  exact ih (j + 1, lp') m2 (by dsimp only; omega)
                    ⟨by omega, hlen', hpre', hin', hm2⟩
                · intro J_if hJ_if
                  c0_hstraight; c0_hsplit
                  · have hpn : n.toNat + j < w.toNat := by
                      have h1 :
                          n.setWidth 64 + (BitVec.ofNat 32 j).setWidth 64 < w.setWidth 64 := hc
                      rw [BitVec.lt_def, hpos_toNat, bv32_setWidth64_toNat] at h1; exact h1
                    clear hc
                    have hpos32_toNat :
                        ((n.setWidth 64 + (BitVec.ofNat 32 j).setWidth 64).setWidth 32).toNat =
                        n.toNat + j := by
                      rw [BitVec.toNat_setWidth, hpos_toNat,
                        Nat.mod_eq_of_lt (by have := w.isLt; omega)]
                    have hsrc_sw :
                        ((aOff + (n.setWidth 64 + (BitVec.ofNat 32 j).setWidth 64).setWidth
                          32).setWidth 64).toNat = aOff.toNat + (n.toNat + j) := by
                      rw [bv32_setWidth64_toNat, BitVec.toNat_add, hpos32_toNat,
                        Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps
                    have hstep := pureOp_loop_step (idxFn := idxFn)
                      (srcIdx := ((aOff + (n.setWidth 64 + (BitVec.ofNat 32 j).setWidth 64).setWidth
                        32).setWidth 64).toNat)
                      hlp_len hpre hin (by rw [hlp_len]; omega) (by rw [hsrc_sw]; omega)
                      (by rw [hsrc_sw, hlp_len]; omega)
                      (by rw [hsrc_sw]; simp only [idxFn, hpn, ↓reduceIte])
                    rw [hout_sw] at *
                    exact hJ_if _ ⟨_, hstep.1, hstep.2.1, hstep.2.2, sep_ac hm⟩
                  · have hpn : ¬ n.toNat + j < w.toNat := by
                      have h1 :
                          ¬ n.setWidth 64 + (BitVec.ofNat 32 j).setWidth 64 < w.setWidth 64 := hc
                      rw [BitVec.lt_def, hpos_toNat, bv32_setWidth64_toNat] at h1; exact h1
                    clear hc
                    c0_hsteps
                    have hsign_eq : litsPool[((aOff + (w - 1#32)).setWidth 64).toNat]'(by
                          rw [hsign_sw, hcap]; omega) =
                        litsPool.getD (idxFn j) 0#32 := by
                      rw [← ops_getD_eq_getElem litsPool 0#32 (by rw [hsign_sw, hcap]; omega),
                        hsign_sw]
                      simp only [idxFn, ite_eq_right hpn]
                    have hstep := pureOp_loop_step_val (idxFn := idxFn) hlp_len hpre hin
                      (by rw [hlp_len]; omega) hsign_eq
                    rw [hout_sw] at *
                    exact hJ_if _ ⟨_, hstep.1, hstep.2.1, hstep.2.2, sep_ac hm⟩
              · have hj_eq : j = w.toNat := by
                  have h1 : ¬ BitVec.ofNat 32 j < w := hc
                  rw [BitVec.lt_def, BitVec.toNat_ofNat,
                    Nat.mod_eq_of_lt (by have := w.isLt; omega)] at h1
                  omega
                clear hc; c0_hsteps
                exact pureOp_ok_close (ok := okFn) hok_t hoom0 hlp_len hpre
                  (fun k hk => hin k (hj_eq ▸ hk)) hml hQ
      · have hcond : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
            w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) := fun h => hfit h.2.2
        rw [ite_eq_right hcond]; dsimp only; rw [ite_eq_right (fun h => h hoom0)]
        intro m1 hm1
        have hfail : okFn hdr = false := by simp [okFn, hoom0, hsl_t, hfit]
        c0_hstraight; c0_hsplit
        · clear hc; c0_hsteps; exact pureOp_oom_close (ok := okFn) hfail (sep_ac hm1) hQ
        · exfalso; cases hc
    · exact hJ_bad m ⟨rfl, Or.inr (by cases hok : sliceOkBool hdr aOff w <;> simp_all)⟩

theorem bv_blast_reverse_wp (Γ : Env)
    (hSlice : Γ.Has "bv_slice_ok" smBvSliceOkSpec)
    (hAlloc : Γ.Has "bv_lits_alloc" bvLitsAllocSpec) :
    ∀ xs m Q X, bvBlastReverseSpec xs m Q X → Func.wp Γ bv_blast_reverse_body xs m Q X := by
  rintro ⟨h, aOff, w, ⟨⟩⟩ m Q X ⟨hdr, litsPool, R, hcap, hm, hQ⟩
  let okFn : BVHdrState → Bool := fun hd =>
    decide (hd.oom = 0#32 ∧ sliceOkBool hd aOff w = true ∧
      w.toNat ≤ hd.lits_cap.toNat - hd.lits_len.toNat)
  let idxFn : Nat → Nat := fun j => aOff.toNat + (w.toNat - 1 - j)
  c0_hstraight
  refine wp_join0 (fun m_bad => m_bad = m ∧ (hdr.oom ≠ 0#32 ∨ sliceOkBool hdr aOff w = false))
    ?_ ?_
  · intro _ m_bad ⟨hm_bad, hbad⟩; subst hm_bad
    c0_hsteps
    exact pureOp_oom_close (ok := okFn) (pureOp_bad_decide_false hbad) (sep_ac hm) hQ
  · intro J_bad hJ_bad
    c0_hstraight; c0_hsplit
    · exact hJ_bad m ⟨rfl, Or.inl (by c0_bv_omega [hc])⟩
    have hoom0 : hdr.oom = 0#32 := by c0_bv_omega [hc]
    clear hc; c0_hstraight
    c0_hcall hSlice; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
    c0_hsplit
    · have hsl_t : sliceOkBool hdr aOff w = true := by
        cases hok : sliceOkBool hdr aOff w <;> simp_all
      clear hc hJ_bad; c0_hstraight
      c0_hcall hAlloc; refine ⟨hdr, array (t := i32) hdr.lits_ptr litsPool ⋆ R, sep_ac hm, ?_⟩
      by_cases hfit : w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat
      · have ⟨hcond, hbd_all⟩ := pureOp_guard_false_alloc hcap hoom0 hsl_t hfit
        rw [ite_eq_left hcond]; intro m1 hm1
        have hok_t : okFn hdr = true := by simp [okFn, hoom0, hsl_t, hfit]
        let hdr1 : BVHdrState := { hdr with lits_len := hdr.lits_len + w }
        c0_hstraight; c0_hsplit
        · exfalso; exact hc hoom0
        · clear hc
          have hsl' := hsl_t; rw [sliceOkBool_true_iff] at hsl'
          c0_hstraight
          refine wp_while_state (α := Nat × List (BitVec 32))
            (fun (j, _) => (BitVec.ofNat 32 j, ())) (fun (j, _) => w.toNat - j)
            (fun (j, lp) ml => j ≤ w.toNat ∧ lp.length = litsPool.length ∧
              (∀ p < hdr.lits_len.toNat, lp.getD p 0#32 = litsPool.getD p 0#32) ∧
              (∀ k < j, lp.getD (hdr.lits_len.toNat + k) 0#32 = litsPool.getD (idxFn k) 0#32) ∧
              (bvHdrMem h hdr1 ⋆ array (t := i32) hdr1.lits_ptr lp ⋆ R) ml) ?_ ?_
          · intro J hJ; c0_hsteps
            change (bvHdrMem h hdr1 ⋆ (array (t := i32) hdr1.lits_ptr litsPool ⋆ R)) m1 at hm1
            exact hJ (0, litsPool) m1
              ⟨Nat.zero_le _, rfl, fun _ _ => rfl, fun _ hk => by omega, sep_ac hm1⟩
          · intro J ⟨j, lp⟩ ml ⟨hj_le, hlp_len, hpre, hin, hml⟩ ih
            c0_hstraight; c0_hsplit
            · have hj_lt : j < w.toNat := by
                have h1 : BitVec.ofNat 32 j < w := hc
                rw [BitVec.lt_def, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by have := w.isLt; omega)] at h1
                exact h1
              clear hc
              have hj32 : (BitVec.ofNat 32 j).toNat = j := by
                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := w.isLt; omega)]
              have hout_sw :
                  ((hdr.lits_len + BitVec.ofNat 32 j).setWidth 64).toNat =
                  hdr.lits_len.toNat + j := by
                rw [bv32_setWidth64_toNat, BitVec.toNat_add, hj32, Nat.mod_eq_of_lt (by omega)]
              have hsrc_sw :
                  ((aOff + (w - 1#32 - BitVec.ofNat 32 j)).setWidth 64).toNat =
                  aOff.toNat + (w.toNat - 1 - j) := by
                have hw1 : (w - 1#32).toNat = w.toNat - 1 := by
                  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr
                    (by rw [show (1#32 : BitVec 32).toNat = 1 from rfl]; omega))]; rfl
                have hw2 : (w - 1#32 - BitVec.ofNat 32 j).toNat = w.toNat - 1 - j := by
                  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by rw [hw1, hj32]; omega)),
                    hw1, hj32]
                rw [bv32_setWidth64_toNat, BitVec.toNat_add, hw2, Nat.mod_eq_of_lt (by omega)]
              c0_hstraight
              rw [pureOp_bv32_succ_add (by have := w.isLt; omega)]
              have hstep := pureOp_loop_step (idxFn := idxFn)
                (srcIdx := ((aOff + (w - 1#32 - BitVec.ofNat 32 j)).setWidth 64).toNat)
                hlp_len hpre hin (by rw [hlp_len]; omega) (by rw [hsrc_sw]; omega)
                (by rw [hsrc_sw, hlp_len]; omega)
                (by rw [hsrc_sw])
              rw [hout_sw] at *
              exact ih (j + 1, _) _ (by dsimp only; omega)
                ⟨by omega, hstep.1, hstep.2.1, hstep.2.2, sep_ac hm⟩
            · have hj_eq : j = w.toNat := by
                have h1 : ¬ BitVec.ofNat 32 j < w := hc
                rw [BitVec.lt_def, BitVec.toNat_ofNat,
                  Nat.mod_eq_of_lt (by have := w.isLt; omega)] at h1
                omega
              clear hc; c0_hsteps
              exact pureOp_ok_close (ok := okFn) hok_t hoom0 hlp_len hpre
                (fun k hk => hin k (hj_eq ▸ hk)) hml hQ
      · have hcond : ¬ (hdr.oom = 0#32 ∧ hdr.lits_len.toNat ≤ hdr.lits_cap.toNat ∧
            w.toNat ≤ hdr.lits_cap.toNat - hdr.lits_len.toNat) := fun h => hfit h.2.2
        rw [ite_eq_right hcond]; dsimp only; rw [ite_eq_right (fun h => h hoom0)]
        intro m1 hm1
        have hfail : okFn hdr = false := by simp [okFn, hoom0, hsl_t, hfit]
        c0_hstraight; c0_hsplit
        · clear hc; c0_hsteps; exact pureOp_oom_close (ok := okFn) hfail (sep_ac hm1) hQ
        · exfalso; cases hc
    · exact hJ_bad m ⟨rfl, Or.inr (by cases hok : sliceOkBool hdr aOff w <;> simp_all)⟩

end

end LeanQbe.T.Examples.Bitblast.Proof
